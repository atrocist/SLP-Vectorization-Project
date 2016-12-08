/*
 * File: SLP_C.c
 *
 * Description:
 *   Stub for SLP in C. This is where you implement your SLP pass.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <assert.h>

/* LLVM Header Files */
#include "llvm-c/Core.h"
#include "dominance.h"

/* Header file global to this project */
#include "cfg.h"
#include "loop.h"
#include "worklist.h"
#include "valmap.h"

static LLVMBuilderRef Builder;
int stats[6] = {0};


typedef struct VectorPairDef {
  LLVMValueRef pair[2];//holds isomorphic insts
  int insertAt0;
  struct VectorPairDef *next;
  struct VectorPairDef *prev;
} VectorPair;

//list contains a list of vector pairs added using add pair
//list form is operands->operands->iso pair
typedef struct  {
  VectorPair *head;
  VectorPair *tail;
  valmap_t    visited;//instructions already added in one of the pairs
  valmap_t    sliceA;
  int size;  
  int score;
} VectorList;

static VectorList* create() {
  VectorList *new = (VectorList*) malloc(sizeof(VectorList));
  new->head = NULL;//no pairs
  new->tail = NULL;
  new->visited = valmap_create();
  new->sliceA = valmap_create();
  new->size=0;
  return new;
}

//destroy vector list
static void destroy(VectorList *list)
{
  if(list == NULL){
	return;  
	}
  valmap_destroy(list->visited);
  valmap_destroy(list->sliceA);
  VectorPair *head = list->head;
  VectorPair *tmp;
  while(head) {
    tmp = head;
    head=head->next;
    free(tmp);    
  }
  free(list);
  list = NULL;
}

static int dom(LLVMValueRef a, LLVMValueRef b)
{
  if (LLVMGetInstructionParent(a)!=LLVMGetInstructionParent(b)) {
    LLVMValueRef fun = LLVMGetBasicBlockParent(LLVMGetInstructionParent(a));
    // a dom b?
    return LLVMDominates(fun,LLVMGetInstructionParent(a),
			 LLVMGetInstructionParent(b));
  }

  // a and b must be in same block
  // which one comes first?
  LLVMValueRef t = a;
  while(t!=NULL) {
    if (t==b)
      return 1;
    t = LLVMGetNextInstruction(t);
  }
  return 0;
}

static int dominBB(LLVMValueRef a, LLVMValueRef b)
{
  if (LLVMGetInstructionParent(a)!=LLVMGetInstructionParent(b)) {
 		printf("a and b should be in same BB this should not happen\n");
		exit(0);
 	}

  // a and b must be in same block
  // which one comes first?
  LLVMValueRef t = a;
  while(t!=NULL) {
    if (t==b)
      return 1;
    t = LLVMGetNextInstruction(t);
  }
  return 0;
}

//inserts a pair into vector list
static VectorPair *addPair(VectorList *list, LLVMValueRef a, LLVMValueRef b)
{
  VectorPair *new = (VectorPair*) malloc(sizeof(VectorPair));
  new->pair[0] = a;
  new->pair[1] = b;

  new->insertAt0 = 1;
  valmap_insert(list->visited,a,(void*)1);
  valmap_insert(list->visited,b,(void*)1);
  new->next = NULL;
  new->prev = NULL;
  // empty list so
  // insert at head
  if (list->head==NULL) {
    list->head = new;
    list->tail = new;
  } else {
    // find right place to insert
    VectorPair *temp = list->head;
    VectorPair *prev = NULL;

	//insert after the last instruction that dominates a (it is assumed that a dominates b)
    while(temp && dom(temp->pair[0],a)) {
      prev=temp;
      temp=temp->next;   
    }
	//not insert first
    if (prev) {
      new->next = temp;
      new->prev = prev;
      prev->next = new;
      if (temp) //if not at end
	temp->prev = new;
      else
	list->tail = new;
    } else {//insert first
      list->head->prev = new;
      new->next = list->head;
      list->head = new;
    }
  }  
  list->size++;
  return new;
}

// put a and b into a vector
static LLVMValueRef assembleVec2(LLVMValueRef a, LLVMValueRef b)
{
  LLVMTypeRef type = LLVMTypeOf(a);
  LLVMValueRef ret;

  if (LLVMIsAConstant(a) && LLVMIsAConstant(b)) {
    // Build constant vector
    LLVMValueRef vec[2] = {a,b};
    ret = LLVMConstVector(vec,2);        
  }  else {
    // Build vector of size 2 and type same as a
    LLVMTypeRef vtype = LLVMVectorType(type,2);
    LLVMValueRef c = LLVMConstNull(vtype);
    
	//insert first element
    ret = LLVMBuildInsertElement(Builder,c,a,
				 LLVMConstInt(LLVMInt32Type(),0,0),"v.ie");
	//insert second element
    ret = LLVMBuildInsertElement(Builder,ret,b,
				 LLVMConstInt(LLVMInt32Type(),1,0),"v.ie");    
  }

  return ret;
}

static bool IsIsomorphic(LLVMValueRef I, LLVMValueRef J)
{
	int i=0;
	//I and J should be instructions
	if((!LLVMIsAInstruction(I)) || (!LLVMIsAInstruction(J))){
		return false;	
	}
	//their opcodes should be same
	if(LLVMGetInstructionOpcode(I) != LLVMGetInstructionOpcode(J)){
		return false;	
	}
	//types should be same
	if(LLVMTypeOf(I) != LLVMTypeOf(J)){
		return false;
	}
	//number of operands should be same
	if(LLVMGetNumOperands(I) != LLVMGetNumOperands(J)){
		return false;	
	}
	//type of all operands must match
	for(i=0;i<LLVMGetNumOperands(I);i++){
		if(LLVMIsAInstruction(LLVMGetOperand(I,i)) && LLVMIsAInstruction(LLVMGetOperand(J,i))){
			if(LLVMTypeOf(LLVMGetOperand(I,i)) != LLVMTypeOf(LLVMGetOperand(J,i))){
				return false;
			}		
		}else{
			//operand is not an inst???what to do in such case? not isomorphic = too conservative??
			return false;	
		}
	}
//	printf("found isomorphic pair\n");
	return true;
}

static bool CheckDependence(LLVMValueRef I, LLVMValueRef J)
{
	int i = 0;
	//both should be instructions
	if((!LLVMIsAInstruction(I)) || (!LLVMIsAInstruction(J))){
		return false;	
	}
	//if not in same BB no need to check dependency..consider independent
	if(LLVMGetInstructionParent(I) != LLVMGetInstructionParent(J)){
		return false;	
	}
	//is it equal to J? 
	if(I == J){
		return true;	
	}
	//check dependency along the chain of operands
	for(i = 0;i<LLVMGetNumOperands(I);i++){
		if(LLVMIsAInstruction(LLVMGetOperand(I,i))){
			if(CheckDependence(LLVMGetOperand(I,i),J) == true){
				return true;	
			}	
		}else{
		//what to do if an operand is not an instruction should we mark it independent or dependent or just ignore
		//	return false;	
		}
	}
	return false;
	
}

static bool IsFloat(LLVMValueRef I)
{
	switch(LLVMGetTypeKind(LLVMTypeOf(I))){
		case LLVMHalfTypeKind:
		case LLVMFloatTypeKind:
		case LLVMDoubleTypeKind:
		case LLVMX86_FP80TypeKind:
		case LLVMFP128TypeKind:
		case LLVMPPC_FP128TypeKind:
			return true;
		default:
			return false;
	}	
}

static bool IsIntFloatDoubleAlloca(LLVMValueRef I)
{
	switch(LLVMGetTypeKind(LLVMGetElementType(LLVMTypeOf(I)))){
		case LLVMHalfTypeKind:
		case LLVMFloatTypeKind:
		case LLVMDoubleTypeKind:
		case LLVMX86_FP80TypeKind:
		case LLVMFP128TypeKind:
		case LLVMPPC_FP128TypeKind:
		case LLVMIntegerTypeKind:
			return true;
		default:
			return false;
	}
	
}

static bool IsIntFloatPtr(LLVMValueRef I){

	switch(LLVMGetTypeKind(LLVMTypeOf(I))){
		case LLVMHalfTypeKind:
		case LLVMFloatTypeKind:
		case LLVMDoubleTypeKind:
		case LLVMX86_FP80TypeKind:
		case LLVMFP128TypeKind:
		case LLVMPPC_FP128TypeKind:
		case LLVMIntegerTypeKind:
		case LLVMPointerTypeKind:
			return true;
		default:
			return false;
	}
	
}

static bool ShouldVectorize(LLVMValueRef I, LLVMValueRef J)
{
	//if typeof I not integer float or ptr
	if(IsIntFloatPtr(I) == false){
		return false;	
	}
	//if I and J are not in same BB
	if(LLVMGetInstructionParent(I) != LLVMGetInstructionParent(J)){
		return false;	
	}
	//if I is a terminator
	if(LLVMIsATerminatorInst(I)){
		return false;	
	}

	//if I is a PHI, Call, Atomic*,ICmp, FCmp, Extract*,Insert*,AddrSpaceCast:
	switch(LLVMGetInstructionOpcode(I)){
	case LLVMRet:
	case LLVMBr:
	case LLVMSwitch:
	case LLVMIndirectBr:
	case LLVMInvoke:
	case LLVMUnreachable: 	
//	case LLVMAdd:
//	case LLVMFAdd: 	
//	case LLVMSub:	
//	case LLVMFSub: 	
//	case LLVMMul: 	
//	case LLVMFMul: 	
//	case LLVMUDiv: 	
//	case LLVMSDiv: 	
//	case LLVMFDiv: 	
//	case LLVMURem: 	
//	case LLVMSRem: 	
//	case LLVMFRem: 	
//	case LLVMShl:	
//	case LLVMLShr: 	
//	case LLVMAShr: 	
//	case LLVMAnd: 	
//	case LLVMOr: 	
//	case LLVMXor: 	
//	case LLVMAlloca: 	
//	case LLVMLoad: 	
//	case LLVMStore: 	
	case LLVMGetElementPtr:
	case LLVMTrunc:
	case LLVMZExt: 	
	case LLVMSExt: 	
	case LLVMFPToUI: 	
	case LLVMFPToSI: 	
	case LLVMUIToFP: 	
	case LLVMSIToFP: 	
	case LLVMFPTrunc: 	
	case LLVMFPExt:
	case LLVMPtrToInt: 	
	case LLVMIntToPtr:	
//try to vectorize all before this
	case LLVMBitCast:
	case LLVMAddrSpaceCast: 	
	case LLVMICmp:
	case LLVMFCmp:	
	case LLVMPHI:
	case LLVMCall: 	
	case LLVMSelect: 	
	case LLVMUserOp1: 	
	case LLVMUserOp2:	
	case LLVMVAArg:
	case LLVMExtractElement:
	case LLVMInsertElement:
	case LLVMShuffleVector:	
	case LLVMExtractValue:
	case LLVMInsertValue:
	case LLVMFence:
	case LLVMAtomicCmpXchg:
	case LLVMAtomicRMW:	
	case LLVMResume:
	case LLVMLandingPad:
			return false;
	default:
		break;
	}
	
	if(LLVMIsALoadInst(I)){
		//if I is a volatile load
		if(LLVMGetVolatile(I)){
			return false;
		}
		//if I is a load that comes from an alloca that holds the address of an integer, float, or double
		if(LLVMIsAAllocaInst(LLVMGetOperand(I,0))){
			if(IsIntFloatDoubleAlloca(LLVMGetOperand(I,0))){
				return true;
			}else
				return false;	
		}else{
			return false;	
		}
	}

	if(LLVMIsAStoreInst(I)){
		//if I is a volatile store
		if(LLVMGetVolatile(I)){
			return false;
		}
		//if I is a load that comes from an alloca that holds the address of an integer, float, or double
		if(LLVMIsAAllocaInst(LLVMGetOperand(I,1))){
			if(IsIntFloatDoubleAlloca(LLVMGetOperand(I,1))){
				return true;
			}else
				return false;	
		}else{
			return false;	
		}
	}

	//check dependency inside BB
	//I is dependent on J: // you must consider full backward slice of I within BB
	if(CheckDependence(I,J) == true){
		return false;
	}
	return true;
}

static VectorList* CollectIsomorphicInsts(VectorList* oldList, LLVMValueRef I, LLVMValueRef J)
{
	VectorList* List = NULL;
	int i = 0;
	
	//check params
	if( I == NULL || J == NULL){
		return NULL;
	}
	//if shouldvectorize I,J
	if(!ShouldVectorize(I,J))
	{
		return NULL;
	}
	List = oldList;
	if(List == NULL){
		List = create();	
	}
	//if I or J already in list return list
	if(valmap_check(List->visited,I) || valmap_check(List->visited,J)){
		return List;	
	}
	//insert I or J in dom order
	if(dominBB(I,J))
		addPair(List,I,J);
	else
		addPair(List,J,I);

	for(i=0;i<LLVMGetNumOperands(I);i++){
		if(LLVMIsConstant(LLVMGetOperand(I,i)) && LLVMIsConstant(LLVMGetOperand(I,i))){
			//how to handle constants???
			//not adding constants too conservative?
//			continue;	
		}
		//if operands are instructions check if they can be added to the list
		if(LLVMIsAInstruction(LLVMGetOperand(I,i)) && LLVMIsAInstruction(LLVMGetOperand(J,i))){
			if(IsIsomorphic(LLVMGetOperand(I,i),LLVMGetOperand(J,i))){
				CollectIsomorphicInsts(List,LLVMGetOperand(I,i),LLVMGetOperand(J,i));	
			}
		}
	}
	return List;
}

static bool UsedOutside(LLVMValueRef I, VectorList* List)
{
	LLVMUseRef U;
	for(U = LLVMGetFirstUse(I);U!=NULL;U=LLVMGetNextUse(U)){
			//if any of uses of I are not present in the list
			if(!valmap_check(List->visited,LLVMGetUser(U))){
				return true;	
			}
	}
	return false;
}

static bool NotDefined(LLVMValueRef I, VectorList* List)
{
	//if I is in the list it is defined return false
	if(valmap_check(List->visited,I)){
		return false;	
	}
	return true;
}

static int CalcScore(VectorList* List)
{
	int score = 0;
	int i = 0;
	LLVMValueRef I,J;
	VectorPair *ptr = NULL;
	//foreach pair (I,J) in L:
	for(ptr = List->head; ptr!=NULL; ptr=ptr->next){
		I = ptr->pair[0];	
		J = ptr->pair[1];
		//if TypeOf(I) is floating point kind:
		if(IsFloat(I)){
			score-=4;	
		}else{
			score--;	
		}
		//if I is ev er used outside of L:
		if(UsedOutside(I,List)){
			score++;	
		}
		//if J is ev er used outside of L:
		if(UsedOutside(J,List)){
			score++;	
		}

		//for each operand,op, in I:
		for(i=0;i<LLVMGetNumOperands(I);i++){
			if(LLVMIsAInstruction(LLVMGetOperand(I,i))){
				//if op is not defined by an instruction in L:
				if(NotDefined(LLVMGetOperand(I,i),List)){
					score++;	
				}		
			}
		}
		//for each operand,op, in J:
		for(i=0;i<LLVMGetNumOperands(J);i++){
			if(LLVMIsAInstruction(LLVMGetOperand(J,i))){
				//if op is not defined by an instruction in L:
				if(NotDefined(LLVMGetOperand(J,i),List)){
					score++;	
				}
			}
		}
	}
	return score;
}

static bool IsTransformable(VectorPair* ptr)
{
	LLVMValueRef I,J,K;
	int i=0,flag = 0;
	LLVMUseRef U;
	I=ptr->pair[0];
	J=ptr->pair[1];

	LLVMBasicBlockRef BB = LLVMGetInstructionParent(I);
	for(K=LLVMGetFirstInstruction(BB);K!=NULL;K=LLVMGetNextInstruction(K)){
		flag = 0;
		//check if position is dominated by all operands
		for(i=0;i<LLVMGetNumOperands(I);i++){
			if(LLVMIsAInstruction(LLVMGetOperand(I,i)) && LLVMIsAInstruction(LLVMGetOperand(J,i))){
				if(!(dom(LLVMGetOperand(I,i),K)) || !(dom(LLVMGetOperand(J,i),K))){
						flag = 1;
						break;
				}
			}
		}
		//check if position dominates all uses
		for(U = LLVMGetFirstUse(I);U!=NULL;U=LLVMGetNextUse(U)){
				if(!dom(K,LLVMGetUser(U))){
					flag =1;	
					break;
				}
		}
		for(U = LLVMGetFirstUse(J);U!=NULL;U=LLVMGetNextUse(U)){
				if(!dom(K,LLVMGetUser(U))){
					flag = 1;
					break;
				}
		}
		if(flag == 0){
			//this position dominates all uses and is dominated by all operands
			LLVMPositionBuilderBefore(Builder,K);
			return true;
		}
	}
	return false;
}
//Note:
//isomorphic pairs are transformable if the vector can be placed such that
//it dominates all uses of pair and it is dominated by all operands of the pair

//using gcc:extension variable length array
static LLVMValueRef Build(LLVMValueRef I,LLVMOpcode opcode,int size, LLVMValueRef ops[size],valmap_t op2vec)
{
	int i = 0;
	LLVMValueRef newinsn = NULL;
	LLVMValueRef operands[size];
	for(i=0;i<LLVMGetNumOperands(I);i++){
		operands[i] = LLVMGetOperand(I,i);	
	}

	switch(opcode){
		case LLVMAdd:
				newinsn = LLVMBuildAdd (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMFAdd: 	
				newinsn = LLVMBuildFAdd (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMSub:	
				newinsn = LLVMBuildSub (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMFSub: 	
				newinsn = LLVMBuildFSub (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMMul: 	
				newinsn = LLVMBuildMul (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMFMul: 	
				newinsn = LLVMBuildFMul (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMUDiv: 	
				newinsn = LLVMBuildUDiv (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMSDiv: 	
				newinsn = LLVMBuildSDiv (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMFDiv: 
				newinsn = LLVMBuildFDiv (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;			
		case LLVMURem: 	
				newinsn = LLVMBuildURem (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMSRem: 	
				newinsn = LLVMBuildSRem (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMFRem: 	
				newinsn = LLVMBuildFRem (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMShl:	
				newinsn = LLVMBuildShl (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMLShr: 	
				newinsn = LLVMBuildLShr (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMAShr: 	
				newinsn = LLVMBuildAShr (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMAnd: 	
				newinsn = LLVMBuildAnd (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMOr: 	
				newinsn = LLVMBuildOr (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMXor: 	
				newinsn = LLVMBuildXor (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[1]), "");
				break;
		case LLVMAlloca: 	
				newinsn = LLVMBuildAlloca (Builder, LLVMPointerType(LLVMTypeOf((LLVMValueRef)valmap_find(op2vec,operands[0])),0), "");
				break;
		case LLVMLoad:
				newinsn = LLVMBuildLoad (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),"");
				break;
		case LLVMStore: 	
				newinsn = LLVMBuildStore (Builder, (LLVMValueRef)valmap_find(op2vec,operands[0]),(LLVMValueRef)valmap_find(op2vec,operands[0]));
				break;
//		case LLVMGetElementPtr:
//		case LLVMTrunc:
//		case LLVMZExt: 	
//		case LLVMSExt: 	
//		case LLVMFPToUI: 	
//		case LLVMFPToSI: 	
//		case LLVMUIToFP: 	
//		case LLVMSIToFP: 	
//		case LLVMFPTrunc: 	
//		case LLVMFPExt:
//		case LLVMPtrToInt: 	
//		case LLVMIntToPtr:	
//		case LLVMBitCast:
			break;
		default:
			printf("Vectorization not supported for this instruction\n");
			break;
	}
	return newinsn;

}

static void Vectorize(VectorList* List)
{
	VectorPair *ptr = NULL;
	int i=0, flag =0;
	LLVMValueRef I,J,newinsn,ev;
	//create a valmap that maps original values (key) to vector values (data)
	valmap_t op2vec;
	return;
	op2vec = valmap_create();
	//for each pair (I,J) in L in dominance order:
	for(ptr=List->head;ptr!=NULL;ptr=ptr->next){
		I=ptr->pair[0];
		J=ptr->pair[1];
		//using gcc extension: variable length array of vectors
		LLVMValueRef ops[LLVMGetNumOperands(I)];
		for(i=0;i<LLVMGetNumOperands(I);i++){
			if(LLVMIsAInstruction(LLVMGetOperand(I,i)) && LLVMIsAInstruction(LLVMGetOperand(J,i)) ){
				//if vmap[Op(I,i)] is not found:
				if(!valmap_check(op2vec,LLVMGetOperand(I,i))){
					//corner case: operands of load are not vectorized
					if(LLVMIsALoadInst(I)){
						flag = 1;
						break;
					}
					//ops[i] = packVector(op(I,i),op(J,i))
					if(LLVMGetNextInstruction(LLVMGetOperand(J,i))){
						LLVMPositionBuilderBefore(Builder,LLVMGetNextInstruction(LLVMGetOperand(J,i)));
					}else{
						LLVMPositionBuilderAtEnd(Builder,LLVMGetInstructionParent(LLVMGetOperand(J,i)));
					}
					ops[i] = assembleVec2(LLVMGetOperand(I,i),LLVMGetOperand(J,i));
					//vmap[op(I,i)] = ops[i]
					valmap_insert(op2vec,LLVMGetOperand(I,i),(void*)(ops[i]));
					//vmap[op(J,i)] = ops[i]
					valmap_insert(op2vec,LLVMGetOperand(J,i),(void*)(ops[i]));
				}else{
					//ops[i] = vmap[op(I)]
					ops[i] = (LLVMValueRef)valmap_find(op2vec,LLVMGetOperand(I,i));
				}
			}
		}
		if(flag == 1){
			ptr->insertAt0 = 0;
			flag = 0;
			continue;	
		}
		// Position builder just before I or J, pick the one later in BB
		//but will this guarantee that it dominates all the uses of J??
/*		if(dominBB(I,J)){
			LLVMPositionBuilderBefore(Builder,J);	
		}else{
			LLVMPositionBuilderBefore(Builder,I);							
		}*/
		if(IsTransformable(ptr) == false){
			printf("Error: this should not happen there should be a position to place the vector insn\n");	
		}
		//implement the generic vector insn builder
		newinsn = Build(I,LLVMGetInstructionOpcode(I),LLVMGetNumOperands(I),ops,op2vec);
//
		valmap_insert(op2vec,I,(void*)newinsn);
		valmap_insert(op2vec,J,(void*)newinsn);
	}
	for(ptr=List->head;ptr!=NULL;ptr=ptr->next){
		LLVMValueRef indices[2];
		I = ptr->pair[0];
		J = ptr->pair[1];
		if(ptr->insertAt0 != 1)
			continue;
		//if I has uses:
		if(LLVMGetFirstUse(I) != NULL){
			// Reposition builder
			if(LLVMGetNextInstruction((LLVMValueRef)valmap_find(op2vec,I))){
				LLVMPositionBuilderBefore (Builder,LLVMGetNextInstruction((LLVMValueRef)valmap_find(op2vec,I)));
			}else{
				LLVMPositionBuilderAtEnd(Builder,LLVMGetInstructionParent((LLVMValueRef)valmap_find(op2vec,I)));
			}
			//ev = BuildExtractElement(vmap[I],0) // index 0
			if(LLVMIsAAllocaInst(I)){
				indices[0] = LLVMConstInt(LLVMInt32Type(), (unsigned int)0, 0) ;
				indices[1] = LLVMConstInt(LLVMInt32Type(), (unsigned int)0, 0) ;
				ev = LLVMBuildGEP(Builder,(LLVMValueRef)valmap_find(op2vec,I),indices,(unsigned int)2,"");	
			}else{
				ev = LLVMBuildExtractElement (Builder, (LLVMValueRef)valmap_find(op2vec,I), LLVMConstInt(LLVMInt32Type(), (unsigned int)0, 0), "");
			}
			LLVMReplaceAllUsesWith(I,ev);
			LLVMInstructionEraseFromParent(I);
		}
		if(LLVMGetFirstUse(J) != NULL){
			// Reposition builder
			if(LLVMGetNextInstruction((LLVMValueRef)valmap_find(op2vec,J))){
				LLVMPositionBuilderBefore (Builder,LLVMGetNextInstruction((LLVMValueRef)valmap_find(op2vec,J)));
			}else{
				LLVMPositionBuilderAtEnd(Builder,LLVMGetInstructionParent((LLVMValueRef)valmap_find(op2vec,J)));
			}
			//ev = BuildExtractElement(vmap[J],0) // index 1
			if(LLVMIsAAllocaInst(J)){
				indices[0] = LLVMConstInt(LLVMInt32Type(), (unsigned int)0, 0) ;
				indices[1] = LLVMConstInt(LLVMInt32Type(), (unsigned int)0, 1) ;
				ev = LLVMBuildGEP(Builder,(LLVMValueRef)valmap_find(op2vec,J),indices,(unsigned int)2,"");	
			}else{
				ev = LLVMBuildExtractElement (Builder, (LLVMValueRef)valmap_find(op2vec,J), LLVMConstInt(LLVMInt32Type(), (unsigned int)1, 0), "");
			}
			LLVMReplaceAllUsesWith(J,ev);
			LLVMInstructionEraseFromParent(J);
		}		
	}
	valmap_destroy(op2vec);
	//Remove any dead extractelements we inserted
}


static void printList(VectorList *List)
{
	VectorPair* ptr = NULL;
	printf("VectorList instruction pairs:\n");
	for(ptr=List->head;ptr!=NULL;ptr=ptr->next)
	{
		printf("%s\n",LLVMPrintValueToString(ptr->pair[0]));
		printf("%s\n",LLVMPrintValueToString(ptr->pair[1]));
	}
}

static void SLPOnBasicBlock(LLVMBasicBlockRef BB)
{
  LLVMValueRef I, J;
  int changed;
  int i=0;
  VectorList *old_best_list = NULL;
  VectorList *newList;
  VectorPair *ptr = NULL;
 //1 pass per block
 do {
    changed = 0;
    
	old_best_list=NULL;
	//for each instruction I in BB
	//start from last instruction and keep searching for isomorphic insts
	for(I=LLVMGetLastInstruction(BB);
   	   I!=NULL;
   	   I=LLVMGetPreviousInstruction(I))
   	 {      
      	// find a match with I
		//for each instruction J such that J comes before I
		for(J=LLVMGetFirstInstruction(BB);J!=I;J=LLVMGetNextInstruction(J)){
			//if isomorphic(I,J)
			if(IsIsomorphic(I,J)){
	 			newList = NULL;
				//list = collectisomorphicinsta(list,I,J)
				newList = CollectIsomorphicInsts(newList,I,J);
				if(newList == NULL){
					continue;	
				}
				//if size of list>=2
				if(newList->size<2){
					destroy(newList);
					newList = NULL;
					continue;
				}
				//if it is transformable
/*				for(ptr=newList->head;ptr!=NULL;ptr=ptr->next){
					if(!IsTransformable(ptr)){
						destroy(newList);
						newList = NULL;
						break;
					}	
				}
				if(newList == NULL){
					continue;	
				}*/
				//calc score
				newList->score=CalcScore(newList);
				//this is first list no prev best list
				if(old_best_list == NULL){
					old_best_list = newList;
					newList = NULL;
					continue;	
				}
				//if score is best score replace best list
				//old list was there replace old
				if(newList->score < old_best_list->score){
/*					for(ptr=newList->head;ptr!=NULL;ptr=ptr->next){
						if(!IsTransformable(ptr)){
							destroy(newList);
							newList = NULL;
							break;
						}	
					}
					if(newList == NULL){
						continue;	
					}*/
					destroy(old_best_list);
					old_best_list = NULL;
					old_best_list = newList;
					newList = NULL;
				}else{
					//score is not best discard list
					destroy(newList);
					newList = NULL;
				}
			}
		}
    }
	//found best list
	if(old_best_list){
		for(ptr=old_best_list->head;ptr!=NULL;ptr=ptr->next){
			if(!IsTransformable(ptr)){
				destroy(old_best_list);
				old_best_list = NULL;
				break;
			}	
		}
		if(old_best_list){
		//update stats
			if(old_best_list->size > 5){
				stats[5]++;	
			}else{
				stats[old_best_list->size]++;
			}
			//vectorize the list
			printList(old_best_list);
			Vectorize(old_best_list);
//			printf("vectorized a  list\n");
			//destroy the list
			destroy(old_best_list);
			old_best_list = NULL;
	//		printf("yes\t");
			//changed the BB move on to next BB since i=1
			changed = 1;	
		}
	}
	i++;
  } while(changed && i<3);//loop while changes are being made or number of lists created is less than 3
}

static void SLPOnFunction(LLVMValueRef F) 
{
  LLVMBasicBlockRef BB;
  for(BB=LLVMGetFirstBasicBlock(F);
      BB!=NULL;
      BB=LLVMGetNextBasicBlock(BB))
    {
      SLPOnBasicBlock(BB);
    }
}

void SLP_C(LLVMModuleRef Module)
{
  LLVMValueRef F;
  int i=0;
	Builder = LLVMCreateBuilder();
  for(F=LLVMGetFirstFunction(Module); 
      F!=NULL;
      F=LLVMGetNextFunction(F))
    {
      SLPOnFunction(F);
    }
	printf("SLP Results\n");
	printf("SIZE:\tCount\n");
	for(i=2;i<6;i++){
			printf("%4d:\t%d\n",i,stats[i]);
	}
}




