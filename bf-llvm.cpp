#include <boost/foreach.hpp>
#include <fstream>
#include <iostream>
#include <llvm/ADT/STLExtras.h>
#include <llvm/ADT/Statistic.h>
#include <llvm/Analysis/DebugInfo.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/Bitcode/ReaderWriter.h>
#include <llvm/CallingConv.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/JIT.h>
#include <llvm/Function.h>
#include <llvm/Instructions.h>
#include <llvm/Intrinsics.h>
#include <llvm/LLVMContext.h>
#include <llvm/LinkAllPasses.h>
#include <llvm/Metadata.h>
#include <llvm/Module.h>
#include <llvm/PassManager.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/IRBuilder.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/raw_os_ostream.h>
#include <llvm/Support/system_error.h>
#include <llvm/Target/TargetData.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <llvm/Transforms/Utils/Local.h>
#include <stack>
#include <sysexits.h>

#define foreach BOOST_FOREACH

using namespace std;
using namespace llvm;
using namespace llvm::dwarf;

struct MyLoopInfo
{
   Value* beforeValue;
   PHINode* startValue;
   Value* endValue;
   Value* afterValue;

   BasicBlock* beforeBlock;
   BasicBlock* startBlock;
   BasicBlock* endBlock;
   BasicBlock* afterBlock;
};

Function* makeFunc(Module* module, const char* const source, size_t tapeSize = 256)
{
   // Some useful types and constants
   IntegerType* cellType = IntegerType::get(module->getContext(), CHAR_BIT);
   Constant* one = ConstantInt::get(cellType, 1);
   IntegerType* intType = Type::getIntNTy(module->getContext(), sizeof(int) * CHAR_BIT);
   IntegerType* sizeType = Type::getIntNTy(module->getContext(), sizeof(size_t) * CHAR_BIT);
   ConstantInt* tapeSizeV = ConstantInt::get(sizeType, tapeSize);

   //declare i32 @getchar()
   Function* getchar = cast<Function>(module->getOrInsertFunction("getchar", intType, NULL));
   getchar->setCallingConv(CallingConv::C);
   getchar->setDoesNotThrow(true);

   //declare i32 @putchar(i32 %c) nounwind
   Function* putchar = cast<Function>(module->getOrInsertFunction("putchar", intType, intType, NULL));
   putchar->setCallingConv(CallingConv::C);
   putchar->setDoesNotThrow(true);

   //declare i64 @fwrite(i8* nocapture, i64, i64, %struct._IO_FILE* nocapture) nounwind
   Function* fwrite = cast<Function>(module->getOrInsertFunction("fwrite", sizeType, Type::getInt8PtrTy(module->getContext()), sizeType, sizeType, Type::getInt8PtrTy(module->getContext()), NULL));
   fwrite->setDoesNotThrow(true);

   // Contruct void main(char* tape)
   Function* main = cast<Function>(module->getOrInsertFunction("main", intType, NULL));
   main->setCallingConv(CallingConv::C);
   BasicBlock* block = BasicBlock::Create(module->getContext(), "code", main);

   stack<MyLoopInfo> loops;
   IRBuilder<> codeIR(block);

   Value* tape = codeIR.CreateAlloca(cellType, tapeSizeV, "tape");
   codeIR.CreateMemSet(tape, Constant::getNullValue(cellType), tapeSizeV, 0);
   Value* head = ConstantInt::get(sizeType, 0);
   for (const char* s = source; *s; ++s)
   {
      char pos_label[32];
      snprintf(pos_label, sizeof(pos_label), "src_chr_%010d", static_cast<int>(s - source));
      codeIR.SetInsertPoint(block);

      switch(*s)
      {
         case '>':
         {
             head = codeIR.CreateAdd(head, ConstantInt::get(head->getType(), 1), pos_label);
             break;
         }
         case '<':
         {
             head = codeIR.CreateSub(head, ConstantInt::get(head->getType(), 1), pos_label);
             break;
         }
         case '+':
         {
             Value* headPtr = codeIR.CreateInBoundsGEP(tape, head);
             Value* headValue = codeIR.CreateLoad(headPtr);
             Value* result = codeIR.CreateAdd(headValue, one, pos_label);
             codeIR.CreateStore(result, headPtr);
             break;
         }
         case '-':
         {
             Value* headPtr = codeIR.CreateInBoundsGEP(tape, head);
             Value* headValue = codeIR.CreateLoad(headPtr);
             Value* result = codeIR.CreateSub(headValue, one, pos_label);
             codeIR.CreateStore(result, headPtr);
             break;
         }
         case '.':
         {
             Value* headPtr = codeIR.CreateInBoundsGEP(tape, head);
             Value* headValue = codeIR.CreateLoad(headPtr);
             Value* c = codeIR.CreateZExt(headValue, intType, pos_label);
             codeIR.CreateCall(putchar, c);
             break;
         }
         case ',':
         {
             Value* headPtr = codeIR.CreateInBoundsGEP(tape, head);
             Value* input = codeIR.CreateCall(getchar, pos_label);
             codeIR.CreateStore(input, headPtr);
             break;
         }
         case '[':
         {
             // Construct loop info
             MyLoopInfo loop;
             loop.beforeBlock = block;
             loop.startBlock = BasicBlock::Create(module->getContext(), pos_label, main);
             loop.afterBlock = BasicBlock::Create(module->getContext(), "", main);
             loop.beforeValue = head;

             // Create branching instructions
             Value* headPtr = codeIR.CreateInBoundsGEP(tape, head);
             Value* headValue = codeIR.CreateLoad(headPtr);
             Value* condition = codeIR.CreateIsNotNull(headValue);
             codeIR.CreateCondBr(condition, loop.startBlock, loop.afterBlock);

             // Create a phi node
             codeIR.SetInsertPoint(loop.startBlock);
             loop.startValue = codeIR.CreatePHI(loop.beforeValue->getType(), 1, "head");
             loop.startValue->addIncoming(loop.beforeValue, loop.beforeBlock);

             // Push the loop
             loops.push(loop);
             block = loop.startBlock;
             head = loop.startValue;
             break;
         }
         case ']':
         {
             // Retrieve the loop info
             MyLoopInfo loop = loops.top(); loops.pop();
	     loop.endValue = head;
             loop.endBlock = block;

             // Create a conditional branch
             Value* headPtr = codeIR.CreateInBoundsGEP(tape, head);
             Value* headValue = codeIR.CreateLoad(headPtr);
             Value* condition = codeIR.CreateIsNotNull(headValue);
             loop.afterBlock->setName(pos_label);
             codeIR.CreateCondBr(condition, loop.startBlock, loop.afterBlock);

             // Augement loops phi node
             loop.startValue->addIncoming(loop.endValue, loop.endBlock);

             // Switch to the after block
             block = loop.afterBlock;
             break;
         }
         default:
            break;
      }
   }

   // Close the function
   codeIR.SetInsertPoint(block);
   codeIR.CreateRet(ConstantInt::get(intType, 0));

   return main;
}

struct PutCharAggregatePass : public BasicBlockPass
{
    static char ID;
    PutCharAggregatePass() :
        BasicBlockPass(ID)
    {
    }

    virtual bool runOnBasicBlock(BasicBlock& B)
    {
#if 0
        errs() << "PutCharAggregatePass: ";
        errs().write_escaped(B.getParent()->getName()) << ": ";
        errs().write_escaped(B.getName()) << "\n";
#endif
        return false;
    }
};

char PutCharAggregatePass::ID;

#if 0
//===-- CondPropagate.cpp - Propagate Conditional Expressions -------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass propagates information about conditional expressions through the
// program, allowing it to eliminate conditional branches in some cases.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "condprop"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/Pass.h"
#include "llvm/Type.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Streams.h"
using namespace llvm;
#endif

STATISTIC(NumBrThread, "Number of CFG edges threaded through branches");
STATISTIC(NumSwThread, "Number of CFG edges threaded through switches");

namespace {
  struct CondProp : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    CondProp() : FunctionPass(ID) {}

    virtual bool runOnFunction(Function &F);

#if 0
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequiredID(BreakCriticalEdgesID);
      //AU.addRequired<DominanceFrontier>();
    }
#endif

  private:
    bool MadeChange;
    void SimplifyBlock(BasicBlock *BB);
    void SimplifyPredecessors(BranchInst *BI);
    void SimplifyPredecessors(SwitchInst *SI);
    void RevectorBlockTo(BasicBlock *FromBB, BasicBlock *ToBB);
  };

  char CondProp::ID;
  //RegisterPass<CondProp> X("condprop", "Conditional Propagation");
}

bool CondProp::runOnFunction(Function &F) {
  bool EverMadeChange = false;

  // While we are simplifying blocks, keep iterating.
  do {
    MadeChange = false;
    for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB)
      SimplifyBlock(BB);
    EverMadeChange = EverMadeChange || MadeChange;
  } while (MadeChange);
  return EverMadeChange;
}

void CondProp::SimplifyBlock(BasicBlock *BB) {
  if (BranchInst *BI = dyn_cast<BranchInst>(BB->getTerminator())) {
    // If this is a conditional branch based on a phi node that is defined in
    // this block, see if we can simplify predecessors of this block.
    if (BI->isConditional() && isa<PHINode>(BI->getCondition()) &&
        cast<PHINode>(BI->getCondition())->getParent() == BB)
      SimplifyPredecessors(BI);

  } else if (SwitchInst *SI = dyn_cast<SwitchInst>(BB->getTerminator())) {
    if (isa<PHINode>(SI->getCondition()) &&
        cast<PHINode>(SI->getCondition())->getParent() == BB)
      SimplifyPredecessors(SI);
  }

  // If possible, simplify the terminator of this block.
  if (ConstantFoldTerminator(BB))
    MadeChange = true;

  // If this block ends with an unconditional branch and the only successor has
  // only this block as a predecessor, merge the two blocks together.
  if (BranchInst *BI = dyn_cast<BranchInst>(BB->getTerminator()))
    if (BI->isUnconditional() && BI->getSuccessor(0)->getSinglePredecessor() &&
        BB != BI->getSuccessor(0)) {
      BasicBlock *Succ = BI->getSuccessor(0);

      // If Succ has any PHI nodes, they are all single-entry PHI's.
      while (PHINode *PN = dyn_cast<PHINode>(Succ->begin())) {
        assert(PN->getNumIncomingValues() == 1 &&
               "PHI doesn't match parent block");
        PN->replaceAllUsesWith(PN->getIncomingValue(0));
        PN->eraseFromParent();
      }

      // Remove BI.
      BI->eraseFromParent();

      // Move over all of the instructions.
      BB->getInstList().splice(BB->end(), Succ->getInstList());

      // Any phi nodes that had entries for Succ now have entries from BB.
      Succ->replaceAllUsesWith(BB);

      // Succ is now dead, but we cannot delete it without potentially
      // invalidating iterators elsewhere.  Just insert an unreachable
      // instruction in it.
      new UnreachableInst(BB->getContext(), Succ);
      MadeChange = true;
    }
}

// SimplifyPredecessors(branches) - We know that BI is a conditional branch
// based on a PHI node defined in this block.  If the phi node contains constant
// operands, then the blocks corresponding to those operands can be modified to
// jump directly to the destination instead of going through this block.
void CondProp::SimplifyPredecessors(BranchInst *BI) {
  // TODO: We currently only handle the most trival case, where the PHI node has
  // one use (the branch), and is the only instruction besides the branch in the
  // block.
  PHINode *PN = cast<PHINode>(BI->getCondition());
  if (!PN->hasOneUse()) return;

  BasicBlock *BB = BI->getParent();
  if (&*BB->begin() != PN || &*next(BB->begin()) != BI)
    return;

  // Ok, we have this really simple case, walk the PHI operands, looking for
  // constants.  Walk from the end to remove operands from the end when
  // possible, and to avoid invalidating "i".
  for (unsigned i = PN->getNumIncomingValues(); i != 0; --i)
    if (ConstantInt *CB = dyn_cast<ConstantInt>(PN->getIncomingValue(i-1))) {
      // If we have a constant, forward the edge from its current to its
      // ultimate destination.
      RevectorBlockTo(PN->getIncomingBlock(i-1),
                      BI->getSuccessor(CB->isZero()));
      ++NumBrThread;

      // If there were two predecessors before this simplification, or if the
      // PHI node contained all the same value except for the one we just
      // substituted, the PHI node may be deleted.  Don't iterate through it the
      // last time.
      if (BI->getCondition() != PN) return;
    }
}

// SimplifyPredecessors(switch) - We know that SI is switch based on a PHI node
// defined in this block.  If the phi node contains constant operands, then the
// blocks corresponding to those operands can be modified to jump directly to
// the destination instead of going through this block.
void CondProp::SimplifyPredecessors(SwitchInst *SI) {
  // TODO: We currently only handle the most trival case, where the PHI node has
  // one use (the branch), and is the only instruction besides the branch in the
  // block.
  PHINode *PN = cast<PHINode>(SI->getCondition());
  if (!PN->hasOneUse()) return;

  BasicBlock *BB = SI->getParent();
  if (&*BB->begin() != PN || &*next(BB->begin()) != SI)
    return;

  bool RemovedPreds = false;

  // Ok, we have this really simple case, walk the PHI operands, looking for
  // constants.  Walk from the end to remove operands from the end when
  // possible, and to avoid invalidating "i".
  for (unsigned i = PN->getNumIncomingValues(); i != 0; --i)
    if (ConstantInt *CI = dyn_cast<ConstantInt>(PN->getIncomingValue(i-1))) {
      // If we have a constant, forward the edge from its current to its
      // ultimate destination.
      unsigned DestCase = SI->findCaseValue(CI);
      RevectorBlockTo(PN->getIncomingBlock(i-1),
                      SI->getSuccessor(DestCase));
      ++NumSwThread;
      RemovedPreds = true;

      // If there were two predecessors before this simplification, or if the
      // PHI node contained all the same value except for the one we just
      // substituted, the PHI node may be deleted.  Don't iterate through it the
      // last time.
      if (SI->getCondition() != PN) return;
    }
}


// RevectorBlockTo - Revector the unconditional branch at the end of FromBB to
// the ToBB block, which is one of the successors of its current successor.
void CondProp::RevectorBlockTo(BasicBlock *FromBB, BasicBlock *ToBB) {
  BranchInst *FromBr = cast<BranchInst>(FromBB->getTerminator());
  assert(FromBr->isUnconditional() && "FromBB should end with uncond br!");

  // Get the old block we are threading through.
  BasicBlock *OldSucc = FromBr->getSuccessor(0);

  // OldSucc had multiple successors. If ToBB has multiple predecessors, then 
  // the edge between them would be critical, which we already took care of.
  // If ToBB has single operand PHI node then take care of it here.
  while (PHINode *PN = dyn_cast<PHINode>(ToBB->begin())) {
    assert(PN->getNumIncomingValues() == 1 && "Critical Edge Found!");    
    PN->replaceAllUsesWith(PN->getIncomingValue(0));
    PN->eraseFromParent();
  }

  // Update PHI nodes in OldSucc to know that FromBB no longer branches to it.
  OldSucc->removePredecessor(FromBB);

  // Change FromBr to branch to the new destination.
  FromBr->setSuccessor(0, ToBB);

  MadeChange = true;
}

int main(int argc, char* argv[])
{
   if(argc < 2)
   {
      cerr << "Usage: " << argv[0] << " bf_file" << endl;
      return -1;
   }
   ifstream sourceFile(argv[1]);
   string line, source;
   while(getline(sourceFile, line)) source += line;

   // Setup a module and engine for JIT-ing
   std::string error;
   InitializeNativeTarget();

   Module* module = new Module("bfcode", getGlobalContext());

   InitializeNativeTarget();
   LLVMLinkInJIT();
   ExecutionEngine *engine = EngineBuilder(module)
      .setErrorStr(&error)
      .setOptLevel(CodeGenOpt::Aggressive)
      .create();
   if(!engine)
   {
      cout << "No engine created: " << error << endl;
      return -1;
   }

   module->setDataLayout(engine->getTargetData()->getStringRepresentation());

   // Compile the BF to IR
   cout << "Parsing… " << flush;
   Function* func = makeFunc(module, source.c_str());
   cout << "done" << endl;

   {
       ofstream dst("out.ll");
       raw_os_ostream rawdst(dst);
       rawdst << *module;
   }

   // Run optimization passes
   cout << "Optimizing… " << flush;

   PassManagerBuilder PMBuilder;

   FunctionPassManager pm(module);
   PMBuilder.populateFunctionPassManager(pm);
   pm.add(new TargetData(*(engine->getTargetData())));
   pm.add(createVerifierPass());

   // Eliminate simple loops such as [>>++<<-]
   pm.add(createInstructionCombiningPass()); // Cleanup for scalarrepl.
   pm.add(createLICMPass());                 // Hoist loop invariants
   pm.add(createPromoteMemoryToRegisterPass());
   pm.add(createIndVarSimplifyPass());       // Canonicalize indvars
   pm.add(createLoopDeletionPass());         // Delete dead loops
   pm.add(createConstantPropagationPass());  // Propagate constants
   pm.add(new CondProp);                     // Propagate conditionals

   // Simplify code
   for(int repeat=0; repeat < 3; repeat++)
   {
      pm.add(createPromoteMemoryToRegisterPass());
      pm.add(createGVNPass());                  // Remove redundancies
      pm.add(createSCCPPass());                 // Constant prop with SCCP
      pm.add(createLoopDeletionPass());
      pm.add(createLoopUnrollPass());
      pm.add(createCFGSimplificationPass());    // Merge & remove BBs
      pm.add(createInstructionCombiningPass());
      pm.add(createConstantPropagationPass());  // Propagate constants
      pm.add(createAggressiveDCEPass());        // Delete dead instructions
      pm.add(createCFGSimplificationPass());    // Merge & remove BBs
      pm.add(createDeadStoreEliminationPass()); // Delete dead stores
      pm.add(createMemCpyOptPass());            // Combine multiple stores into memset's
      //pm.add(new PutCharAggregatePass);
   }

   pm.add(createPromoteMemoryToRegisterPass());

   // Process
   foreach (Function& f, *module)
       if (!f.isDeclaration)
           pm.run(f);

   PassManager pmm;

   PMBuilder.populateModulePassManager(pmm);
   pmm.add(createConstantMergePass());
   pmm.add(createGlobalOptimizerPass());
   pmm.add(createGlobalDCEPass());
   pmm.add(createIPConstantPropagationPass());
   pmm.run(*module);

   foreach (Function& f, *module)
       if (!f.isDeclaration)
           pm.run(f);
   pmm.run(*module);

   cout << "done" << endl;

   {
       ofstream dst("optout.ll");
       raw_os_ostream rawdst(dst);
       rawdst << *module;
   }

   // Compile …
   cout << "Compiling…" << flush;
   int (*bf)() = (int (*)())engine->getPointerToFunction(func);
   cout << " done" << endl;

   // … and run!
   return bf();
}
