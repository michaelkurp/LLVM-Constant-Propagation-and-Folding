#include "llvm/ADT/Statistic.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/ConstantFolding.h"

#include <map>
#include <set>
#include <iostream>
#include <string>

using namespace llvm;

#define DEBUG_TYPE "lab"

namespace {
  struct Lab : public BasicBlockPass {
    static char ID;

    Lab() : BasicBlockPass(ID) {}
    bool isConstant(Value * op, int& constant){
      Value *op0 = op;
      if(Instruction *CI = dyn_cast<Instruction>(op))
        op0 = CI->getOperand(0);

      if(ConstantInt * CI = dyn_cast<ConstantInt>(op0))
      {
        if(CI->getBitWidth() <= 32)
        {
          constant = CI->getSExtValue();
          return true;
        }
      }
      return false;
    }
    void foldConst(Instruction*& inst)
    {
      errs() << inst;
      if(isa<BinaryOperator>(inst)){
        std::set<Instruction*> deadBin;
        BinaryOperator *binOp = (BinaryOperator*)inst;
        Value* op1 = binOp->getOperand(0);
        Value* op2 = binOp->getOperand(1);

        int Lconst = 0, Rconst = 0;
        int newConst = 0;

        if(isConstant(op1, Lconst)){
          if(isConstant(op2,Rconst )){
            switch(inst->getOpcode()){
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
            Type* i32int = IntegerType::get(inst->getContext(), 32);
            Constant *val = ConstantInt::getSigned(i32int, newConst);

            Instruction *next = inst->getNextNonDebugInstruction();
            if(StoreInst *nextSI = dyn_cast<StoreInst>(next))
            {
              nextSI->setOperand(0, val);
              deadBin.insert(inst);
            }


          }
        }
    }
    }
    bool runOnBasicBlock(BasicBlock &BB) override {
      LLVMContext &Ctx = BB.getContext();
      llvm::Type *i32_type = llvm::IntegerType::getInt32Ty(Ctx);
      // This map should store the values that we can
      // replace with a constant

      // This should hold any alloca instructions that
      // we can eliminate from the code

      // This should hold any load, store, and other
      // operations that we can remove from the code

      //while(counter != counterPrev){
      //  counterPrev = counter;
      int counter = 0;
      while(true){
        std::map<Value*,ConstantInt*> constants;
        std::set<Instruction*> killDefs;
        std::set<Instruction*> killUses;
      for(Instruction& I : BB){


	        Instruction *inst = &I;

          if(isa<StoreInst>(inst))
          {
            errs() << inst;
            StoreInst *store = (StoreInst*) inst;
            Value *v = store->getValueOperand();
            Value* pointer = store->getPointerOperand();
            if(ConstantInt* cons = dyn_cast<ConstantInt>(v))
            {
              constants[pointer] = cons;
              killUses.insert(store);
              if(AllocaInst* all = dyn_cast<AllocaInst>(pointer))
                killDefs.insert(all);
            }
          }
          if(isa<BinaryOperator>(inst))
          {
            BinaryOperator *binOp = (BinaryOperator*)inst;
            Value* op1 = binOp->getOperand(0);
            Value* op2 = binOp->getOperand(1);


            if(isa<LoadInst>(op1) && isa<ConstantInt>(op2))
            {
              LoadInst *load1 = (LoadInst*) op1;
              Value* pointer1 = load1->getPointerOperand();
              if(constants.count(pointer1) > 0)
              {
                ConstantInt *cons1 = constants[pointer1];
                ConstantInt *cons2 = dyn_cast<ConstantInt>(op2);
                binOp->setOperand(0, cons1);
                binOp->setOperand(1, cons2);
                killUses.insert(load1);
              }
            }

            else if(isa<LoadInst>(op1) && isa<LoadInst>(op2))
            {
              LoadInst *load1 = (LoadInst*) op1;
              LoadInst *load2 = (LoadInst*) op2;

              Value* pointer1 = load1->getPointerOperand();
              Value* pointer2 = load2->getPointerOperand();


              if(constants.count(pointer1) > 0 && constants.count(pointer2) > 0)
              {
                ConstantInt  *cons1 = constants[pointer1];
                ConstantInt   *cons2 = constants[pointer2];
                binOp->setOperand(0, cons1);
                binOp->setOperand(1, cons2);
                killUses.insert(load1);
                killUses.insert(load2);
              }

            }

            else if(isa<LoadInst>(op2) && isa<ConstantInt>(op1))
            {
              LoadInst *load1 = (LoadInst*) op2;
              Value* pointer1 = load1->getPointerOperand();
              if(constants.count(pointer1) > 0)
              {
                ConstantInt *cons1 = constants[pointer1];
                ConstantInt *cons2 = dyn_cast<ConstantInt>(op1);
                binOp->setOperand(0, cons1);
                binOp->setOperand(1, cons2);
                killUses.insert(load1);
              }
            }

        }

	// TODO: Your code goes here
      }
        if(killDefs.size() == 0 && killUses.size() == 0)
          break;
      for(Instruction *I : killUses){
        // eraseFromParent completely removes an instruction
        // from the IR
	         I->eraseFromParent();
           killUses.erase(I);
      }

      for(Instruction *I : killDefs){
	         I->eraseFromParent();
           killDefs.erase(I);
      }
      /*
      std::set<Instruction*> deadBin;

      for(Instruction& I: BB)
      {
        Instruction *inst = &I;

        if(isa<BinaryOperator>(inst)){
          BinaryOperator *binOp = (BinaryOperator*)inst;
          Value* op1 = binOp->getOperand(0);
          Value* op2 = binOp->getOperand(1);

          int Lconst = 0, Rconst = 0;
          int newConst = 0;

          if(isConstant(op1, Lconst)){
            if(isConstant(op2,Rconst )){
              switch(inst->getOpcode()){
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
              Type* i32int = IntegerType::get(I.getContext(), 32);
              Constant *val = ConstantInt::getSigned(i32int, newConst);

              Instruction *next = inst->getNextNonDebugInstruction();
              if(StoreInst *nextSI = dyn_cast<StoreInst>(next))
              {
                nextSI->setOperand(0, val);
                deadBin.insert(inst);
              }


            }
          }
      }

    }
    for(Instruction *I : deadBin)
    {
      I->eraseFromParent();
      deadBin.erase(I);
    }
    */
      break;
    } //End while

      return true;
    }
  };
}

char Lab::ID = 0;
static RegisterPass<Lab> X("optlab", "Optimization Lab Pass");
