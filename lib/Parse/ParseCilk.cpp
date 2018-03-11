//===--- ParseCilk.cpp - Cilk Parsing -------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file implements the Cilk portions of the Parser interface.
//
//===----------------------------------------------------------------------===//

#include "clang/Parse/RAIIObjectsForParser.h"
#include "clang/Parse/Parser.h"

using namespace clang;

/// ParseCilkForStatement
///       cilk-for-statement:
/// [C]     '_Cilk_for' '(' assignment-expr';' condition ';' expr ')' stmt
/// [C++]   '_Cilk_for' '(' for-init-stmt condition ';' expr ')' stmt
StmtResult Parser::ParseCilkForStmt() {
  assert(Tok.is(tok::kw__Cilk_for) && "Not a Cilk for stmt!");
  SourceLocation CilkForLoc = ConsumeToken();  // eat the '_Cilk_for'.

  if (Tok.isNot(tok::l_paren)) {
    Diag(Tok, diag::err_expected_lparen_after) << "_Cilk_for";
    SkipUntil(tok::semi);
    return StmtError();
  }

  bool C99orCXXorObjC = getLangOpts().C99 || getLangOpts().CPlusPlus ||
    getLangOpts().ObjC1;

  // Start the loop scope.
  //
  // A program contains a return, break or goto statement that would transfer
  // control into or out of a _Cilk_for loop is ill-formed.
  //
  unsigned ScopeFlags = 0;
  if (C99orCXXorObjC)
    ScopeFlags |= Scope::DeclScope | Scope::ControlScope;

  ParseScope CilkForScope(this, ScopeFlags);

  BalancedDelimiterTracker T(*this, tok::l_paren);
  T.consumeOpen();

  ExprResult Value;

  bool ForEach = false, ForRange = false;
  StmtResult FirstPart;
  Sema::ConditionResult SecondPart;
  ExprResult Collection;
  ForRangeInit ForRangeInit;
  FullExprArg ThirdPart(Actions);

  if (Tok.is(tok::code_completion)) {
    Actions.CodeCompleteOrdinaryName(getCurScope(),
                                     C99orCXXorObjC ? Sema::PCC_ForInit
                                     : Sema::PCC_Expression);
    cutOffParsing();
    return StmtError();
  }

  ParsedAttributesWithRange attrs(AttrFactory);
  MaybeParseCXX11Attributes(attrs);

  // '_Cilk_for' '(' for-init-stmt
  // '_Cilk_for' '(' assignment-expr;
  if (Tok.is(tok::semi)) {  // _Cilk_for (;
    ProhibitAttributes(attrs);
    // no control variable declaration initialization, eat the ';'.
    Diag(Tok, diag::err_cilk_for_missing_control_variable) << ";";
    ConsumeToken();
  } else if (isForInitDeclaration()) {  // _Cilk_for (int i = 0;
    // Parse declaration, which eats the ';'.
    if (!C99orCXXorObjC)   // Use of C99-style for loops in C90 mode?
      Diag(Tok, diag::ext_c99_variable_decl_in_for_loop);

    SourceLocation DeclStart = Tok.getLocation();
    SourceLocation DeclEnd;

    // Still use Declarator::ForContext. A new enum item CilkForContext
    // may be needed for extra checks.

    DeclGroupPtrTy DG = ParseSimpleDeclaration(DeclaratorContext::ForContext,
                                               DeclEnd, attrs,
                                               /*RequireSemi*/false,
                                               /*ForRangeInit*/nullptr);
    FirstPart = Actions.ActOnDeclStmt(DG, DeclStart, Tok.getLocation());

    if(Tok.is(tok::semi))
      ConsumeToken(); // Eat the ';'.
    else
      Diag(Tok, diag::err_expected_semi_for);
  } else {
    ProhibitAttributes(attrs);
    Value = Actions.CorrectDelayedTyposInExpr(ParseExpression());

    ForEach = isTokIdentifier_in();

    // Turn the expression into a stmt.
    if (!Value.isInvalid()) {
      if (ForEach)
        FirstPart = Actions.ActOnForEachLValueExpr(Value.get());
      else
        FirstPart = Actions.ActOnExprStmt(Value);
    }

    if (Tok.is(tok::semi))
      ConsumeToken(); // Eat the ';'
    else {
      if (!Value.isInvalid()) {
        Diag(Tok, diag::err_expected_semi_for);
      } else {
        // Skip until semicolon or rparen, don't consume it.
        SkipUntil(tok::r_paren, StopAtSemi | StopBeforeMatch);
        if (Tok.is(tok::semi))
          ConsumeToken();
      }
    }
  }

  // True while inside the Cilk for variable capturing region.
  bool InCapturingRegion = false;

  // Parse the second part of the for specifier.
  getCurScope()->AddFlags(Scope::BreakScope | Scope::ContinueScope);
  if (!SecondPart.isInvalid()) {
    // Parse the second part of the for specifier.
    if (Tok.is(tok::semi)) {  // for (...;;
      // no second part.
      Diag(Tok, diag::err_cilk_for_missing_condition)
        << FirstPart.get()->getSourceRange();
    } else if (Tok.is(tok::r_paren)) {
      // missing both semicolons.
      Diag(Tok, diag::err_cilk_for_missing_condition)
        << FirstPart.get()->getSourceRange();
    } else {
      if (getLangOpts().CPlusPlus)
        SecondPart =
            ParseCXXCondition(nullptr, CilkForLoc, Sema::ConditionKind::Boolean);
      else {
        ExprResult SecondExpr = ParseExpression();
        if (SecondExpr.isInvalid())
          SecondPart = Sema::ConditionError();
        else
          SecondPart =
              Actions.ActOnCondition(getCurScope(), CilkForLoc, SecondExpr.get(),
                                     Sema::ConditionKind::Boolean);
      }
    }

    if (Tok.isNot(tok::semi)) {
      if (!SecondPart.isInvalid())
        Diag(Tok, diag::err_expected_semi_for);
      else
        // Skip until semicolon or rparen, don't consume it.
        SkipUntil(tok::r_paren, StopAtSemi | StopBeforeMatch);
    }

    if (Tok.is(tok::semi)) {
      ConsumeToken();
    }

    // Parse the third part of the _Cilk_for specifier.
    if (Tok.isNot(tok::r_paren)) {   // for (...;...;)
      // Enter the variable capturing region for both Cilk for
      // increment and body.
      //
      // For the following Cilk for loop,
      //
      // _Cilk_for (T x = a;  x < b; x += c) {
      //   // body
      // }
      //
      // The outlined function would look like
      //
      // void helper(Context, low, high) {
      //   _index_var = low
      //   x += low * c
      //
      //   while (_index_var < high) {
      //     // body
      //     x += c                // loop increment
      //     _index_var++;
      //   }
      // }
      //
      // The loop increment would be part of the outlined function,
      // together with the loop body. Hence, we enter a capturing region
      // before parsing the loop increment.
      Actions.ActOnStartOfCilkForStmt(CilkForLoc, getCurScope(), FirstPart);
      InCapturingRegion = true;

      ExprResult Third = ParseExpression();
      // FIXME: The C++11 standard doesn't actually say that this is a
      // discarded-value expression, but it clearly should be.
      ThirdPart = Actions.MakeFullDiscardedValueExpr(Third.get());
    } else
      Diag(Tok, diag::err_cilk_for_missing_increment)
        << FirstPart.get()->getSourceRange();      
  }
  // Match the ')'.
  T.consumeClose();

  // TODO: Extend _Cilk_for to support these.
  if (ForRange) {
    Diag(CilkForLoc, diag::err_cilk_for_forrange_loop_not_supported);
    // ExprResult CorrectedRange =
    //     Actions.CorrectDelayedTypoasInExpr(ForRangeInit.RangeExpr.get());
    // ForRangeStmt = Actions.ActOnCXXForRangeStmt(
    //     getCurScope(), ForLoc, CoawaitLoc, FirstPart.get(),
    //     ForRangeInit.ColonLoc, CorrectedRange.get(),
    //     T.getCloseLocation(), Sema::BFRK_Build);


  // Similarly, we need to do the semantic analysis for a for-range
  // statement immediately in order to close over temporaries correctly.
  } else if (ForEach) {
    Diag(CilkForLoc, diag::err_cilk_for_foreach_loop_not_supported);
    // ForEachStmt = Actions.ActOnObjCForCollectionStmt(ForLoc,
    //                                                  FirstPart.get(),
    //                                                  Collection.get(),
    //                                                  T.getCloseLocation());
  }

  // Enter the variable capturing region for Cilk for body.
  if (!InCapturingRegion)
    Actions.ActOnStartOfCilkForStmt(CilkForLoc, getCurScope(), FirstPart);

  // Cannot use goto to exit the Cilk for body.
  ParseScope InnerScope(this, Scope::BlockScope | Scope::FnScope |
                        Scope::DeclScope | Scope::ContinueScope);

  // Read the body statement.
  StmtResult Body(ParseStatement());

  // Pop the body scope if needed.
  InnerScope.Exit();

  // Leave the for-scope.
  CilkForScope.Exit();

  if (!FirstPart.isUsable() || !SecondPart.get().second || !ThirdPart.get() ||
      !Body.isUsable()) {
    Actions.ActOnCilkForStmtError();
    return StmtError();
  }

  if (Actions.CheckIfBodyModifiesLoopControlVar(Body.get())) {
    Actions.ActOnCilkForStmtError();
    return StmtError();
  }

  StmtResult Result = Actions.ActOnCilkForStmt(CilkForLoc, T.getOpenLocation(),
                                               FirstPart.get(), SecondPart,
                                               ThirdPart, T.getCloseLocation(),
                                               Body.get());
  if (Result.isInvalid()) {
    Actions.ActOnCilkForStmtError();
    return StmtError();
  }

  return Result;
}
