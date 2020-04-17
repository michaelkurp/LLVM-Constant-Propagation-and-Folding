#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <stack>
#include <string>

using namespace llvm;

#define DEBUG_TYPE "lab"

namespace {
struct Lab : public BasicBlockPass {
  static char ID;

  Lab() : BasicBlockPass(ID) {}

  // Check if constants have the right size
  bool isConstant(Value *op, int &constant) {
    Value *op0 = op;
    if (Instruction *CI = dyn_cast<Instruction>(op))
      op0 = CI->getOperand(0);

    if (ConstantInt *CI = dyn_cast<ConstantInt>(op0)) {
      if (CI->getBitWidth() <= 32) {
        constant = CI->getSExtValue();
        return true;
      }
    }
    return false;
  }

  // Helper function to fold a  BinOp
  ConstantInt *foldConst(Instruction *&inst) {
    if (isa<BinaryOperator>(inst)) {
      BinaryOperator *binOp = (BinaryOperator *)inst;
      Value *op1 = binOp->getOperand(0);
      Value *op2 = binOp->getOperand(1);
      int Lconst = 0, Rconst = 0;
      int newConst = 0;
      if (isConstant(op1, Lconst)) {
        if (isConstant(op2, Rconst)) {
          switch (inst->getOpcode()) {
          case Instruction::Add: {
            newConst = Lconst + Rconst;
            break;
          }
          case Instruction::Sub: {
            newConst = Lconst - Rconst;
            break;
          }
          case Instruction::Mul: {
            newConst = Lconst * Rconst;
            break;
          }
          case Instruction::SDiv: {
            newConst = Lconst / Rconst;
            break;
          }
          }
          Type *i32int = IntegerType::get(inst->getContext(), 32);
          Constant *val = ConstantInt::get(i32int, newConst);
          ConstantInt *final = dyn_cast<ConstantInt>(val);
          return final;
        }
      }
    }
  }
  bool runOnBasicBlock(BasicBlock &BB) override {
    std::map<Value *, ConstantInt *> mapFromPointertoVal;
    std::map<Value *, StoreInst *> mapFromPointertoStore;
    std::stack<Instruction *> killList;
    std::map<Instruction *, ConstantInt *> foldMe;
    std::set<Instruction *> doNotDelete;
    for (Instruction &I : BB) {
      Instruction *inst = &I;

      if (StoreInst *store = dyn_cast<StoreInst>(inst)) {
        if (CallInst *CI = dyn_cast<CallInst>(store->getOperand(0))) {
          doNotDelete.insert(store);
        } else if (PointerType *PT =
                       dyn_cast<PointerType>(store->getOperand(0)->getType())) {
          if (IntegerType *IT =
                  dyn_cast<IntegerType>(PT->getPointerElementType())) {
            if (IT->getBitWidth() == 8) {
              doNotDelete.insert(store);
              Value *pointer = store->getPointerOperand();
              if (AllocaInst *all = dyn_cast<AllocaInst>(pointer)) {
                for (auto U : all->users()) {
                  if (auto I = dyn_cast<Instruction>(U)) {
                    doNotDelete.insert(I);
                    if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
                      for (auto U2 : LI->users()) {
                        if (Instruction *U2inst = dyn_cast<Instruction>(U2))
                          doNotDelete.insert(U2inst);
                      }
                    }
                  }
                }
              }
            }
          }
        } else {
          Value *v = store->getValueOperand();         // Constant
          Value *pointer = store->getPointerOperand(); // Alloca
          if (ConstantInt *cons = dyn_cast<ConstantInt>(v)) {
            mapFromPointertoVal[pointer] = cons;
          }
          Instruction *ref = dyn_cast<Instruction>(inst->getOperand(0));
          if (foldMe.count(ref) > 0) {
            mapFromPointertoVal[pointer] = foldMe[ref];
            store->setOperand(0, foldMe[ref]);
            killList.push(ref);
          }
        }
      }
      if (isa<BinaryOperator>(inst)) {
        BinaryOperator *binOp = (BinaryOperator *)inst;
        Value *op1 = binOp->getOperand(0);
        Value *op2 = binOp->getOperand(1);

        if (isa<LoadInst>(op1) && isa<ConstantInt>(op2)) {
          LoadInst *load1 = (LoadInst *)op1;
          Value *pointer1 = load1->getPointerOperand();
          if (mapFromPointertoVal.count(pointer1) > 0) {
            ConstantInt *cons1 = mapFromPointertoVal[pointer1];
            ConstantInt *cons2 = dyn_cast<ConstantInt>(op2);
            binOp->setOperand(0, cons1);
            binOp->setOperand(1, cons2);
            killList.push(load1);
          }
        } else if (isa<BinaryOperator>(op1) && isa<LoadInst>(op2)) {
          LoadInst *load1 = (LoadInst *)op2;
          Value *pointer1 = load1->getPointerOperand();

          BinaryOperator *bo = dyn_cast<BinaryOperator>(op1);
          ConstantInt *cons2 = foldMe[bo];

          killList.push(bo);

          if (mapFromPointertoVal.count(pointer1) > 0) {
            ConstantInt *cons1 = mapFromPointertoVal[pointer1];
            binOp->setOperand(0, cons1);
            binOp->setOperand(1, cons2);
          }
        } else if (isa<LoadInst>(op1) && isa<BinaryOperator>(op2)) {
          LoadInst *load1 = (LoadInst *)op1;
          Value *pointer1 = load1->getPointerOperand();

          BinaryOperator *bo = dyn_cast<BinaryOperator>(op2);
          ConstantInt *cons2 = foldMe[bo];

          killList.push(bo);

          if (mapFromPointertoVal.count(pointer1) > 0) {
            ConstantInt *cons1 = mapFromPointertoVal[pointer1];
            binOp->setOperand(0, cons1);
            binOp->setOperand(1, cons2);
          }
        }

        else if (isa<LoadInst>(op1) && isa<LoadInst>(op2)) {
          LoadInst *load1 = (LoadInst *)op1;
          LoadInst *load2 = (LoadInst *)op2;

          Value *pointer1 = load1->getPointerOperand();
          Value *pointer2 = load2->getPointerOperand();

          if (mapFromPointertoVal.count(pointer1) > 0 &&
              mapFromPointertoVal.count(pointer2) > 0) {
            ConstantInt *cons1 = mapFromPointertoVal[pointer1];
            ConstantInt *cons2 = mapFromPointertoVal[pointer2];
            binOp->setOperand(0, cons1);
            binOp->setOperand(1, cons2);
            killList.push(load1);
            killList.push(load2);
          }

        }

        else if (isa<LoadInst>(op2) && isa<ConstantInt>(op1)) {
          LoadInst *load1 = (LoadInst *)op2;
          Value *pointer1 = load1->getPointerOperand();
          if (mapFromPointertoVal.count(pointer1) > 0) {
            ConstantInt *cons1 = mapFromPointertoVal[pointer1];
            ConstantInt *cons2 = dyn_cast<ConstantInt>(op1);
            binOp->setOperand(0, cons1);
            binOp->setOperand(1, cons2);
            killList.push(load1);
          }
        }
        foldMe[inst] = foldConst(inst);
      }
    }

    // Clean up
    while (!killList.empty()) {
      Instruction *death = killList.top();
      killList.pop();
      if (death && (doNotDelete.find(death) == doNotDelete.end()))
        death->eraseFromParent();
    }

    std::set<LoadInst *> danglingLoad;
    for (Instruction &I : BB) {
      Instruction *inst = &I;
      if (LoadInst *li = dyn_cast<LoadInst>(inst)) {
        int count = 0;
        for (auto U : li->users()) {
          count++;
        }
        if (count == 0)
          danglingLoad.insert(li);
      }
    }
    for (auto I : danglingLoad) {
      if (isa<Instruction>(I) && (doNotDelete.find(I) == doNotDelete.end()))
        I->eraseFromParent();
    }

    std::map<AllocaInst *, StoreInst *> allocaToStore;
    for (Instruction &I : BB) {
      Instruction *inst = &I;
      if (StoreInst *si = dyn_cast<StoreInst>(inst)) {
        Value *pointer = si->getPointerOperand(); // Alloca
        if (AllocaInst *all = dyn_cast<AllocaInst>(pointer))
          allocaToStore[all] = si;
      }
    }

    for (Instruction &I : BB) {
      Instruction *inst = &I;
      if (LoadInst *li = dyn_cast<LoadInst>(inst)) {
        Value *pointer1 = li->getPointerOperand();
        if (AllocaInst *all = dyn_cast<AllocaInst>(pointer1)) {
          if (allocaToStore.count(all) > 0) {
            allocaToStore.erase(all);
          }
        }
      }
    }

    auto it = allocaToStore.begin();
    while (it != allocaToStore.end()) {
      AllocaInst *all = it->first;
      for (auto U : all->users()) {
        if (Instruction *in = dyn_cast<Instruction>(U))
          if (doNotDelete.find(in) == doNotDelete.end())
            in->eraseFromParent();
      }
      if (all && (doNotDelete.find(all) == doNotDelete.end()))
        all->eraseFromParent();
      it++;
    }
    return true;
  }
};
} // namespace

char Lab::ID = 0;
static RegisterPass<Lab> X("optlab", "Optimization Lab Pass");
