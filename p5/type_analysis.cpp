#include "ast.hpp"
#include "symbol_table.hpp"
#include "errors.hpp"
#include "types.hpp"
#include "name_analysis.hpp"
#include "type_analysis.hpp"

namespace cminusminus{

TypeAnalysis * TypeAnalysis::build(NameAnalysis * nameAnalysis){
	//To emphasize that type analysis depends on name analysis
	// being complete, a name analysis must be supplied for
	// type analysis to be performed.
	TypeAnalysis * typeAnalysis = new TypeAnalysis();
	auto ast = nameAnalysis->ast;
	typeAnalysis->ast = ast;

	ast->typeAnalysis(typeAnalysis);
	if (typeAnalysis->hasError){
		return nullptr;
	}

	return typeAnalysis;

}

void ProgramNode::typeAnalysis(TypeAnalysis * ta){

	//pass the TypeAnalysis down throughout
	// the entire tree, getting the types for
	// each element in turn and adding them
	// to the ta object's hashMap
	for (auto global : *myGlobals){
		global->typeAnalysis(ta);
	}

	//The type of the program node will never
	// be needed. We can just set it to VOID
	//(Alternatively, we could make our type
	// be error if the DeclListNode is an error)
	ta->nodeType(this, BasicType::produce(VOID));
}

void FnDeclNode::typeAnalysis(TypeAnalysis * ta){

	ta->nodeType(this, ta->getCurrentFnType());
    std::list<const DataType *> * formals = new std::list<const DataType *>();
    for(auto formal : *(this->myFormals))
    {
        auto fType = formal->getTypeNode()->getType();
        formals->push_back(fType);
    }
    auto ret = this->getRetTypeNode()->getType();
    FnType * functionType = new FnType(formals, ret);
    ta->setCurrentFnType(functionType);
    for (auto stmt : *myBody)
    {
        stmt->typeAnalysis(ta);
    }
}

void StmtNode::typeAnalysis(TypeAnalysis * ta){
	TODO("Implement me in the subclass");
}

void AssignStmtNode::typeAnalysis(TypeAnalysis * ta){
	myExp->typeAnalysis(ta);

	//It can be a bit of a pain to write
	// "const DataType *" everywhere, so here
	// the use of auto is used instead to tell the
	// compiler to figure out what the subType variable
	// should be
	auto subType = ta->nodeType(myExp);

	// As error returns null if subType is NOT an error type
	// otherwise, it returns the subType itself
	if (subType->asError()){
		ta->nodeType(this, subType);
	} else {
		ta->nodeType(this, BasicType::produce(VOID));
	}
}

void ExpNode::typeAnalysis(TypeAnalysis * ta){
	TODO("Override me in the subclass");
}

void AssignExpNode::typeAnalysis(TypeAnalysis * ta){
	//TODO: Note that this function is incomplete.
	// and needs additional code

	//Do typeAnalysis on the subexpressions
	myDst->typeAnalysis(ta);
	mySrc->typeAnalysis(ta);

	const DataType * tgtType = ta->nodeType(myDst);
	const DataType * srcType = ta->nodeType(mySrc);

	//While incomplete, this gives you one case for
	// assignment: if the types are exactly the same
	// it is usually ok to do the assignment. One
	// exception is that if both types are function
	// names, it should fail type analysis
	if(tgtType->asError() || srcType->asError()){
		ta->nodeType(this, ErrorType::produce());
		return;
	}

	if(!tgtType->validVarType()){
		ta->errAssignOpd(myDst->pos());
		ta->nodeType(this, ErrorType::produce());
		return;
	}

	if(!srcType->validVarType()){
		ta->errAssignOpd(mySrc->pos());
		ta->nodeType(this, ErrorType::produce());
		return;
	}

	if (tgtType == srcType){
		ta->nodeType(this, tgtType);
		return;
	}

	//Some functions are already defined for you to
	// report type errors. Note that these functions
	// also tell the typeAnalysis object that the
	// analysis has failed, meaning that main.cpp
	// will print "Type check failed" at the end
	ta->errAssignOpr(this->pos());


	//Note that reporting an error does not set the
	// type of the current node, so setting the node
	// type must be done
	ta->nodeType(this, ErrorType::produce());
}

void DeclNode::typeAnalysis(TypeAnalysis * ta){
	TODO("Override me in the subclass");
}

void VarDeclNode::typeAnalysis(TypeAnalysis * ta){
	// VarDecls always pass type analysis, since they
	// are never used in an expression. You may choose
	// to type them void (like this), as discussed in class
	ta->nodeType(this, BasicType::produce(VOID));
}

void IDNode::typeAnalysis(TypeAnalysis * ta){
	// IDs never fail type analysis and always
	// yield the type of their symbol (which
	// depends on their definition)
	ta->nodeType(this, this->getSymbol()->getDataType());
}

void IntLitNode::typeAnalysis(TypeAnalysis * ta){
	// IntLits never fail their type analysis and always
	// yield the type INT
	ta->nodeType(this, BasicType::produce(INT));
}


void CallExpNode::typeAnalysis(TypeAnalysis * ta) {
	for (auto arg : *myArgs)
	{
		arg->typeAnalysis(ta);
	}
	const DataType * idType = myID->getSymbol()->getDataType();
	const FnType * fType = idType->asFn();

	if(fType != nullptr)
	{
		if(myArgs->size() != fType->getFormalTypes()->size())
		{
			ta->errArgCount(myID->pos());
			ta->nodeType(this, ErrorType::produce());
		}
		else
		{
			std::list<ExpNode*>::iterator acItr = myArgs->begin();
			std::list<ExpNode*>::iterator actualsBegin = myArgs->begin();
			auto formalTypesBegin = fType->getFormalTypes()->begin();
			while(acItr != myArgs->end()){

				const DataType * actualType = ta->nodeType(*acItr);
				const ExpNode * actual = *actualsBegin;
				const DataType * formalType =  *formalTypesBegin;

				actualsBegin++;
				acItr++;
				formalTypesBegin++;
				if (!actualType->asError() && !formalType->asError()
				&& formalType != actualType)
				{
					ta->errArgMatch(this->pos());
				}
			}
		}
	}
	else
	{
		ta->errCallee(myID->pos());
		ta->nodeType(this, ErrorType::produce());
		return;
	}

	ta->nodeType(this, fType->getReturnType());
}



void BinaryExpNode::typeAnalysis(TypeAnalysis * ta){

}

void LessNode::typeAnalysis(TypeAnalysis * ta){
	myExp1->typeAnalysis(ta);
	myExp2->typeAnalysis(ta);
	const DataType * left = ta->nodeType(myExp1);
	const DataType * right = ta->nodeType(myExp2);
	if (left->asFn() == nullptr)
	{
				 if (!left->isInt())
				 {
								 ta->errRelOpd(myExp1->pos());
				 }
	}
	else {
				 if (!left->asFn()->getReturnType()->isInt() )
				 {
								 ta->errRelOpd(myExp1->pos());
				 }
	}
	if (right->asFn() == nullptr)
	{
				 if (!right->isInt())
				 {
								 ta->errRelOpd(myExp2->pos());
				 }
	}
	else {
				 if (!right->asFn()->getReturnType()->isInt())
				 {
								 ta->errRelOpd(myExp2->pos());
				 }
	}
	if (!ta->passed())
	{
				 ta->nodeType(this, ErrorType::produce());
	}
	ta->nodeType(this, BasicType::produce(BOOL));
}



void NegNode::typeAnalysis(TypeAnalysis * ta){
myExp->typeAnalysis(ta);
auto subType = ta->nodeType(myExp);
if(!subType->isInt() && !subType->asError()){
	ta->errMathOpd(myExp->pos());
	ta->nodeType(this, ErrorType::produce());
	return;
}
ta->nodeType(this, subType);
}

void NotNode::typeAnalysis(TypeAnalysis * ta){
myExp->typeAnalysis(ta);
auto subType = ta->nodeType(myExp);
if(!subType->isBool() && !subType->asError()){
	ta->errLogicOpd(myExp->pos());
	ta->nodeType(this, ErrorType::produce());
	return;
}
ta->nodeType(this, subType);
}

void StrLitNode::typeAnalysis(TypeAnalysis * ta){
	ta->nodeType(this, BasicType::produce(STRING));
}

void TrueNode::typeAnalysis(TypeAnalysis * ta){
	ta->nodeType(this, BasicType::produce(BOOL));
}
void FalseNode::typeAnalysis(TypeAnalysis * ta){
	ta->nodeType(this, BasicType::produce(BOOL));
}

void PlusNode::typeAnalysis(TypeAnalysis * ta){
	myExp1->typeAnalysis(ta);
	myExp2->typeAnalysis(ta);
	const DataType * left = ta->nodeType(myExp1);
	const DataType * right = ta->nodeType(myExp2);
	if (left->asFn() == nullptr)
	{
		if (!left->isInt())
	 {
			 ta->errMathOpd(this->pos());
	 }
	}
	else {
				 if (!left->asFn()->getReturnType()->isInt())
				 {
								 ta->errMathOpd(this->pos());
				 }
	}
	if (right->asFn() == nullptr)
	{
				 if (!right->isInt())
				 {
								 ta->errMathOpd(this->pos());
				 }
	}
	else {
				 if (!right->asFn()->getReturnType()->isInt())
				 {
								 ta->errMathOpd(this->pos());
				 }
	}
	if (!ta->passed())
	{
				 ta->nodeType(this, ErrorType::produce());
	}
	ta->nodeType(this, BasicType::produce(INT));
}

void MinusNode::typeAnalysis(TypeAnalysis * ta){
	myExp1->typeAnalysis(ta);
  myExp2->typeAnalysis(ta);
  const DataType * left = ta->nodeType(myExp1);
  const DataType * right = ta->nodeType(myExp2);
  if (left->asFn() == nullptr)
  {
     if (!left->isInt())
     {
         ta->errMathOpd(this->pos());
     }
  }
  else {
     if (!left->asFn()->getReturnType()->isInt())
     {
           ta->errMathOpd(this->pos());
     }
  }
  if (right->asFn() == nullptr)
  {
     if (!right->isInt())
     {
         ta->errMathOpd(this->pos());
     }
  }
  else {
     if (!right->asFn()->getReturnType()->isInt())
     {
           ta->errMathOpd(this->pos());
     }
  }
  if (!ta->passed())
  {
     ta->nodeType(this, ErrorType::produce());
  }
  ta->nodeType(this, BasicType::produce(INT));
}

void TimesNode::typeAnalysis(TypeAnalysis * ta){
	myExp1->typeAnalysis(ta);
  myExp2->typeAnalysis(ta);
  const DataType * left = ta->nodeType(myExp1);
  const DataType * right = ta->nodeType(myExp2);
  if (left->asFn() == nullptr)
  {
   	if (!left->isInt())
   {
       ta->errMathOpd(this->pos());
   }
  }
  else {
     if (!left->asFn()->getReturnType()->isInt() )
     {
           ta->errMathOpd(this->pos());
     }
  }
  if (right->asFn() == nullptr)
  {
       if (!right->isInt())
       {
         	ta->errMathOpd(this->pos());
			 }
  }
  else {
     if (!right->asFn()->getReturnType()->isInt())
     {
         ta->errMathOpd(this->pos());
     }
  }
  if (!ta->passed())
  {
       ta->nodeType(this, ErrorType::produce());
  }
  ta->nodeType(this, BasicType::produce(INT));
}

void DivideNode::typeAnalysis(TypeAnalysis * ta){
	myExp1->typeAnalysis(ta);
  myExp2->typeAnalysis(ta);
  const DataType * left = ta->nodeType(myExp1);
  const DataType * right = ta->nodeType(myExp2);
  if (left->asFn() == nullptr)
  {
       if (!left->isInt())
       {
           ta->errMathOpd(this->pos());
       }
  }
  else {
   	if (!left->asFn()->getReturnType()->isInt())
    {
         ta->errMathOpd(this->pos());
     }
  }
  if (right->asFn() == nullptr)
  {
       if (!right->isInt())
       {
           ta->errMathOpd(this->pos());
       }
   }
  else {
     if (!right->asFn()->getReturnType()->isInt() )
     {
         ta->errMathOpd(this->pos());
     }
  }
  if (!ta->passed())
  {
     ta->nodeType(this, ErrorType::produce());
  }
  ta->nodeType(this, BasicType::produce(INT));
}

void AndNode::typeAnalysis(TypeAnalysis * ta) {
	myExp1->typeAnalysis(ta);
  myExp2->typeAnalysis(ta);
  const DataType * left = ta->nodeType(myExp1);
  const DataType * right = ta->nodeType(myExp2);
	if (!left->asBasic()->isBool() || !right->asBasic()->isBool())
	   {
         ta->errLogicOpd(this->pos());
				 ta->nodeType(this, ErrorType::produce());
     }
}

void OrNode::typeAnalysis(TypeAnalysis * ta) {
  myExp1->typeAnalysis(ta);
  myExp2->typeAnalysis(ta);
  const DataType * left = ta->nodeType(myExp1);
  const DataType * right = ta->nodeType(myExp2);
  if (!left->asBasic()->isBool() || !right->asBasic()->isBool())
	   {
         ta->errLogicOpd(this->pos());
				 ta->nodeType(this, ErrorType::produce());
		 }

  }

void ShortLitNode::typeAnalysis(TypeAnalysis * ta){
ta->nodeType(this, BasicType::produce(SHORT));
}

void RefNode::typeAnalysis(TypeAnalysis * ta){
	myID->typeAnalysis(ta);
	ta->nodeType(this, PtrType::produce(ta->nodeType(myID)));
}

void DerefNode::typeAnalysis(TypeAnalysis * ta){
	myID->typeAnalysis(ta);
	auto type = ta->nodeType(myID);
	if(type->asPtr()){
		ta->nodeType(this, type->asPtr()->getBase());
	}
	else{
		ta->errDerefOpd(myID->pos());
		ta->nodeType(this, ErrorType::produce());
	}
}

void CallStmtNode::typeAnalysis(TypeAnalysis * ta){
	myCallExp->typeAnalysis(ta);
		ta->nodeType(this, BasicType::produce(VOID));
}

static bool opdTypeAnalysis(TypeAnalysis * ta, ExpNode * opd, std::string scenarioOpd){
	bool retOpdBool = true;
	opd->typeAnalysis(ta);
	auto which = ta->nodeType(opd);
	if(scenarioOpd == "compareOpd"){
		if(which->isInt()){
			retOpdBool = true;
		}
		else{
			ta-> errRelOpd(opd->pos());
			ta->nodeType(opd, ErrorType::produce());
			retOpdBool = false;
		}
	}
	if(scenarioOpd == "logicalOperatorOpd"){
		if(which->isBool()==true){
			retOpdBool = true;
		}
		else{
			ta->errLogicOpd(opd->pos());
			ta->nodeType(opd, ErrorType::produce());
			retOpdBool = false;
		}
	}
	if(scenarioOpd == "notEqYesOpd"){
		if(which->isInt() == true || which->isBool() == true){
			retOpdBool = true;
		}
		else{
			ta->errEqOpd(opd->pos());
			ta->nodeType(opd, ErrorType::produce());
			retOpdBool = false;
		}
	}
	if(scenarioOpd == "plusMinusTimesDividOpd"){
		if(which->isInt() == true){
			retOpdBool = true;
		}
		else{
			ta->errMathOpd(opd->pos());
			ta->nodeType(opd, ErrorType::produce());
			retOpdBool = false;
		}
	}
	return retOpdBool;
}

/*void BinaryExpNode::notEqYesOperatorAnaylsis(TypeAnalysis * ta){
	bool tmp1 = opdTypeAnalysis(ta, myExp1, "notEqYesOpd");
	bool tmp2 = opdTypeAnalysis(ta, myExp2, "notEqYesOpd");
	if(tmp2 == true && tmp1 == true){
		auto whichtmp1 = ta->nodeType(myExp1);
		auto whichtmp2 = ta->nodeType(myExp2);
		if(whichtmp2 != whichtmp1){
			ta->errEqOpr(this->pos());
			ta->nodeType(this, ErrorType::produce());
			return;
		}
	}
	ta->nodeType(this, BasicType::produce(BOOL));
}
*/
void ReturnStmtNode::typeAnalysis(TypeAnalysis * ta){
	auto funcType = ta->getCurrentFnType();
	auto funcReturnType = funcType->getReturnType();

	if(myExp != NULL){
		if(funcReturnType != BasicType::VOID()){
			myExp->typeAnalysis(ta);
			auto subType = ta->nodeType(myExp);
			if((subType != funcReturnType) && !subType->asError()){
				ta->errRetWrong(myExp->pos());
				ta->nodeType(this, ErrorType::produce());
				return;
			}
		}
		else{
			myExp->typeAnalysis(ta);
			ta->extraRetValue(myExp->pos());
			ta->nodeType(this, ErrorType::produce());
			return;
		}
	}
	else{
		if(funcReturnType != BasicType::VOID()){
			ta->errRetEmpty(this->pos());
			ta->nodeType(this, ErrorType::produce());
			return;
		}
	}
	ta->nodeType(this, BasicType::VOID());
}

void WhileStmtNode::typeAnalysis(TypeAnalysis * ta){
	myCond->typeAnalysis(ta);
		auto condType = ta->nodeType(myCond);
		if(!condType->isBool() && !condType->asError()){
			ta->errWhileCond(myCond->pos());
			ta->nodeType(this, ErrorType::produce());
		}

		for(auto stmt : *myBody){
			stmt->typeAnalysis(ta);
		}
		ta->nodeType(this, BasicType::produce(VOID));
}

void IfElseStmtNode::typeAnalysis(TypeAnalysis * ta){
	myCond->typeAnalysis(ta);
		auto condType = ta->nodeType(myCond);
		if(!condType->isBool() && !condType->asError()){
			ta->errIfCond(myCond->pos());
			ta->nodeType(this, ErrorType::produce());
		}

		for(auto stmt : *myBodyTrue){
			stmt->typeAnalysis(ta);
		}

		for(auto stmt : *myBodyFalse){
			stmt->typeAnalysis(ta);
		}
		ta->nodeType(this, BasicType::produce(VOID));
}

void IfStmtNode::typeAnalysis(TypeAnalysis * ta){
	myCond->typeAnalysis(ta);
		auto condType = ta->nodeType(myCond);
		if(!condType->isBool() && !condType->asError()){
			ta->errIfCond(myCond->pos());
			ta->nodeType(this, ErrorType::produce());
		}

		for(auto stmt : *myBody){
			stmt->typeAnalysis(ta);
		}
		ta->nodeType(this, BasicType::produce(VOID));
}


void PostDecStmtNode::typeAnalysis(TypeAnalysis * ta){
	myLVal->typeAnalysis(ta);
		auto lValType = ta->nodeType(myLVal);
		if(!lValType->isInt())
		{
			ta->errMathOpd(myLVal->pos());
			ta->nodeType(this,ErrorType::produce());
		}
		ta->nodeType(this, BasicType::produce(VOID));
}

void PostIncStmtNode::typeAnalysis(TypeAnalysis * ta){
	myLVal->typeAnalysis(ta);
		auto lValType = ta->nodeType(myLVal);
		if(!lValType->isInt())
		{
			ta->errMathOpd(myLVal->pos());
			ta->nodeType(this,ErrorType::produce());
		}
		ta->nodeType(this, BasicType::produce(VOID));
}

void WriteStmtNode::typeAnalysis(TypeAnalysis * ta){
	mySrc->typeAnalysis(ta);
		auto subType = ta->nodeType(mySrc);
		if(subType->asFn()){
			ta->errWriteFn(mySrc->pos());
			ta->nodeType(this, ErrorType::produce());
		}
		else if(subType->isVoid()){
			ta->errWriteVoid(mySrc->pos());
			ta->nodeType(this, ErrorType::produce());
		}
		else if(subType->isPtr()){
			ta->errReadPtr(mySrc->pos());
			ta->nodeType(this, ErrorType::produce());
		}
		else{
			ta->nodeType(this, BasicType::produce(VOID));
		}
}

void ReadStmtNode::typeAnalysis(TypeAnalysis * ta){
	myDst->typeAnalysis(ta);
		auto subType = ta->nodeType(myDst);
		if(subType->asFn()){
			ta->errAssignFn(myDst->pos());
			ta->nodeType(this, ErrorType::produce());
		}
		else if(subType->isPtr()){
			ta->errReadPtr(myDst->pos());
			ta->nodeType(this, ErrorType::produce());
		}
		else{
			ta->nodeType(this, BasicType::produce(VOID));
		}
}

void UnaryExpNode::typeAnalysis(TypeAnalysis * ta){

}




void EqualsNode::typeAnalysis(TypeAnalysis * ta) {
	bool tmp1 = opdTypeAnalysis(ta, myExp1, "notEqYesOpd");
	bool tmp2 = opdTypeAnalysis(ta, myExp2, "notEqYesOpd");
	if(tmp2 == true && tmp1 == true){
		auto whichtmp1 = ta->nodeType(myExp1);
		auto whichtmp2 = ta->nodeType(myExp2);
		if(whichtmp2 != whichtmp1){
			ta->errEqOpr(this->pos());
			ta->nodeType(this, ErrorType::produce());
			return;
		}
	}
	ta->nodeType(this, BasicType::produce(BOOL));
}

void NotEqualsNode::typeAnalysis(TypeAnalysis * ta) {
	bool tmp1 = opdTypeAnalysis(ta, myExp1, "notEqYesOpd");
	bool tmp2 = opdTypeAnalysis(ta, myExp2, "notEqYesOpd");
	if(tmp2 == true && tmp1 == true){
		auto whichtmp1 = ta->nodeType(myExp1);
		auto whichtmp2 = ta->nodeType(myExp2);
		if(whichtmp2 != whichtmp1){
			ta->errEqOpr(this->pos());
			ta->nodeType(this, ErrorType::produce());
			return;
		}
	}
	ta->nodeType(this, BasicType::produce(BOOL));
}




void LessEqNode::typeAnalysis(TypeAnalysis * ta) {
        myExp1->typeAnalysis(ta);
        myExp2->typeAnalysis(ta);
        const DataType * left = ta->nodeType(myExp1);
        const DataType * right = ta->nodeType(myExp2);
        if (left->asFn() == nullptr)
        {
               if (!left->isInt())
               {
                       ta->errRelOpd(myExp1->pos());
               }
        }
        else {
               if (!left->asFn()->getReturnType()->isInt() )
               {
                       ta->errRelOpd(myExp1->pos());
               }
        }
        if (right->asFn() == nullptr)
        {
               if (!right->isInt())
               {
                       ta->errRelOpd(myExp2->pos());
               }
        }
        else {
               if (!right->asFn()->getReturnType()->isInt())
               {
                       ta->errRelOpd(myExp2->pos());
               }
        }
        if (!ta->passed())
        {
               ta->nodeType(this, ErrorType::produce());
        }
        ta->nodeType(this, BasicType::produce(BOOL));

}



void GreaterNode::typeAnalysis(TypeAnalysis * ta) {
        myExp1->typeAnalysis(ta);
        myExp2->typeAnalysis(ta);
        const DataType * left = ta->nodeType(myExp1);
        const DataType * right = ta->nodeType(myExp2);
        if (left->asFn() == nullptr)
        {
               if (!left->isInt())
               {
                       ta->errRelOpd(myExp1->pos());
               }
        }
        else {
               if (!left->asFn()->getReturnType()->isInt())
               {
                       ta->errRelOpd(myExp1->pos());
               }
        }
        if (right->asFn() == nullptr)
        {
               if (!right->isInt())
               {
                       ta->errRelOpd(myExp2->pos());
               }
        }
        else {
               if (!right->asFn()->getReturnType()->isInt() )
               {
                       ta->errRelOpd(myExp2->pos());
               }
        }
        if (!ta->passed())
        {
               ta->nodeType(this, ErrorType::produce());
        }
        ta->nodeType(this, BasicType::produce(BOOL));

}



void GreaterEqNode::typeAnalysis(TypeAnalysis * ta) {
        myExp1->typeAnalysis(ta);
        myExp2->typeAnalysis(ta);
        const DataType * left = ta->nodeType(myExp1);
        const DataType * right = ta->nodeType(myExp2);
        if (left->asFn() == nullptr)
        {
               if (!left->isInt())
               {
                       ta->errRelOpd(myExp1->pos());
               }
        }
        else {
               if (!left->asFn()->getReturnType()->isInt() )
               {
                       ta->errRelOpd(myExp1->pos());
               }
        }
        if (right->asFn() == nullptr)
        {
               if (!right->isInt())
               {
                       ta->errRelOpd(myExp2->pos());
               }
        }
        else {
               if (!right->asFn()->getReturnType()->isInt() )
               {
                       ta->errRelOpd(myExp2->pos());
               }
        }
        if (!ta->passed())
        {
               ta->nodeType(this, ErrorType::produce());
        }

        ta->nodeType(this, BasicType::produce(BOOL));

}
}
