CXX?=g++ -std=c++0x
CXXFLAGS?=-pedantic -ggdb -g3 -O2 -Wall
LLVM_CPPFLAGS=$(shell llvm-config-3.0 --cppflags)
LLVM_LIBS=$(shell llvm-config-3.0 --ldflags --libs core jit native ipo instrumentation)

all: bf-llvm

bf-llvm: bf-llvm.cpp
	$(CXX) -o $@ $(CXXFLAGS) $(LLVM_CPPFLAGS) $^ $(LLVM_LIBS)

clean:
	$(RM) bf-llvm

.PHONY: all
