// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Rewrite
// Imports: Init Lean.Meta.ACLt Lean.Meta.Match.MatchEqsExt Lean.Meta.AppBuilder Lean.Meta.SynthInstance Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.LinearArith.Simp
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteUsingDecide_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern uint8_t l_instInhabitedBool;
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_isLemma___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Step_result(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteCtorEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__16;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite_x3f___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_inErasedSet___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5;
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Simp_rewrite_x3f___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5;
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3;
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__1;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs___closed__1;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1;
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2;
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5;
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1;
lean_object* l_Lean_Meta_Linear_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4;
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1;
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1;
lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6;
lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__3;
lean_object* l_Lean_Meta_Simp_Step_updateResult(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteCtorEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__1;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4;
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__15;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10;
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ACLt_main_lt(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteUsingDecide_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__1;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__4;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7;
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__3;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3;
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__2;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = l_Lean_Meta_mkEqTrans(x_18, x_24, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_10, 0, x_27);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_10, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_10);
lean_free_object(x_2);
lean_dec(x_21);
lean_dec(x_20);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_10, 0);
lean_inc(x_35);
lean_dec(x_10);
x_36 = l_Lean_Meta_mkEqTrans(x_18, x_35, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_2, 1, x_40);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_2);
lean_dec(x_21);
lean_dec(x_20);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_48 = lean_ctor_get(x_10, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_49 = x_10;
} else {
 lean_dec_ref(x_10);
 x_49 = lean_box(0);
}
x_50 = l_Lean_Meta_mkEqTrans(x_18, x_48, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_51);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_47);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_59 = x_50;
} else {
 lean_dec_ref(x_50);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1;
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_6, 2);
x_14 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_12, x_13, x_1);
lean_dec(x_12);
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_6, 2);
x_19 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_16, x_18, x_1);
lean_dec(x_16);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
x_14 = lean_environment_find(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_9);
x_15 = lean_box(0);
x_16 = l_Lean_Expr_const___override(x_1, x_15);
x_17 = l_Lean_MessageData_ofExpr(x_16);
x_18 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__2;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__5(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
lean_ctor_set(x_9, 0, x_23);
return x_9;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_1);
x_27 = lean_environment_find(x_26, x_1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_box(0);
x_29 = l_Lean_Expr_const___override(x_1, x_28);
x_30 = l_Lean_MessageData_ofExpr(x_29);
x_31 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__2;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__4;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__5(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_ConstantInfo_levelParams(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_12, x_13);
x_15 = l_Lean_Expr_const___override(x_1, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = l_Lean_ConstantInfo_levelParams(x_16);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_18, x_19);
x_21 = l_Lean_Expr_const___override(x_1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_MessageData_ofExpr(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_Lean_MessageData_ofExpr(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_Lean_Expr_fvar___override(x_22);
x_24 = l_Lean_MessageData_ofExpr(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_MessageData_ofSyntax(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lean_MessageData_ofName(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_15, 3);
x_19 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___closed__1;
x_20 = 0;
x_21 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_20);
lean_inc(x_10);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_PersistentArray_push___rarg(x_18, x_22);
lean_ctor_set(x_15, 3, x_23);
x_24 = lean_st_ref_set(x_8, x_15, x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
x_33 = lean_ctor_get(x_15, 2);
x_34 = lean_ctor_get(x_15, 3);
x_35 = lean_ctor_get(x_15, 4);
x_36 = lean_ctor_get(x_15, 5);
x_37 = lean_ctor_get(x_15, 6);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_38 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___closed__1;
x_39 = 0;
x_40 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_12);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_39);
lean_inc(x_10);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_10);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_PersistentArray_push___rarg(x_34, x_41);
x_43 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_32);
lean_ctor_set(x_43, 2, x_33);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_35);
lean_ctor_set(x_43, 5, x_36);
lean_ctor_set(x_43, 6, x_37);
x_44 = lean_st_ref_set(x_8, x_43, x_16);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("discharge", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
x_2 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
x_3 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
x_4 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", failed to synthesize instance", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", failed to assign instance", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nsythesized value", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nis not definitionally equal to", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_12 = l_Lean_Meta_trySynthInstance(x_3, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 5);
lean_inc(x_21);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 3;
lean_ctor_set_uint8(x_14, 5, x_23);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_20);
lean_ctor_set(x_24, 5, x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_16);
lean_inc(x_2);
x_25 = l_Lean_Meta_isExprDefEq(x_2, x_16, x_24, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_30 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6;
x_34 = lean_unbox(x_31);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_apply_8(x_33, x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_indentExpr(x_3);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_indentExpr(x_16);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__16;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_indentExpr(x_2);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_40);
x_55 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_29, x_54, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_apply_8(x_33, x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_37);
if (x_59 == 0)
{
return x_37;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_37, 0);
x_61 = lean_ctor_get(x_37, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_37);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_25);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_25, 0);
lean_dec(x_64);
x_65 = 1;
x_66 = lean_box(x_65);
lean_ctor_set(x_25, 0, x_66);
return x_25;
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_dec(x_25);
x_68 = 1;
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_25);
if (x_71 == 0)
{
return x_25;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_25, 0);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_25);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_75 = lean_ctor_get_uint8(x_14, 0);
x_76 = lean_ctor_get_uint8(x_14, 1);
x_77 = lean_ctor_get_uint8(x_14, 2);
x_78 = lean_ctor_get_uint8(x_14, 3);
x_79 = lean_ctor_get_uint8(x_14, 4);
x_80 = lean_ctor_get_uint8(x_14, 6);
x_81 = lean_ctor_get_uint8(x_14, 7);
x_82 = lean_ctor_get_uint8(x_14, 8);
x_83 = lean_ctor_get_uint8(x_14, 9);
x_84 = lean_ctor_get_uint8(x_14, 10);
x_85 = lean_ctor_get_uint8(x_14, 11);
x_86 = lean_ctor_get_uint8(x_14, 12);
lean_dec(x_14);
x_87 = 3;
x_88 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_88, 0, x_75);
lean_ctor_set_uint8(x_88, 1, x_76);
lean_ctor_set_uint8(x_88, 2, x_77);
lean_ctor_set_uint8(x_88, 3, x_78);
lean_ctor_set_uint8(x_88, 4, x_79);
lean_ctor_set_uint8(x_88, 5, x_87);
lean_ctor_set_uint8(x_88, 6, x_80);
lean_ctor_set_uint8(x_88, 7, x_81);
lean_ctor_set_uint8(x_88, 8, x_82);
lean_ctor_set_uint8(x_88, 9, x_83);
lean_ctor_set_uint8(x_88, 10, x_84);
lean_ctor_set_uint8(x_88, 11, x_85);
lean_ctor_set_uint8(x_88, 12, x_86);
x_89 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_17);
lean_ctor_set(x_89, 2, x_18);
lean_ctor_set(x_89, 3, x_19);
lean_ctor_set(x_89, 4, x_20);
lean_ctor_set(x_89, 5, x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_16);
lean_inc(x_2);
x_90 = l_Lean_Meta_isExprDefEq(x_2, x_16, x_89, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_95 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_94, x_4, x_5, x_6, x_7, x_8, x_9, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6;
x_99 = lean_unbox(x_96);
lean_dec(x_96);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_box(0);
x_101 = lean_apply_8(x_98, x_100, x_4, x_5, x_6, x_7, x_8, x_9, x_97);
return x_101;
}
else
{
lean_object* x_102; 
x_102 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_97);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
x_107 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_indentExpr(x_3);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_indentExpr(x_16);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__16;
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_indentExpr(x_2);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_105);
x_120 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_94, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_104);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_apply_8(x_98, x_121, x_4, x_5, x_6, x_7, x_8, x_9, x_122);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_124 = lean_ctor_get(x_102, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_102, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_126 = x_102;
} else {
 lean_dec_ref(x_102);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_ctor_get(x_90, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_129 = x_90;
} else {
 lean_dec_ref(x_90);
 x_129 = lean_box(0);
}
x_130 = 1;
x_131 = lean_box(x_130);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_128);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_ctor_get(x_90, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_90, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_135 = x_90;
} else {
 lean_dec_ref(x_90);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_13);
lean_dec(x_2);
x_137 = lean_ctor_get(x_12, 1);
lean_inc(x_137);
lean_dec(x_12);
x_138 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_139 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_138, x_4, x_5, x_6, x_7, x_8, x_9, x_137);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6;
x_143 = lean_unbox(x_140);
lean_dec(x_140);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_3);
lean_dec(x_1);
x_144 = lean_box(0);
x_145 = lean_apply_8(x_142, x_144, x_4, x_5, x_6, x_7, x_8, x_9, x_141);
return x_145;
}
else
{
lean_object* x_146; 
x_146 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_141);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
x_151 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10;
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_indentExpr(x_3);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_149);
x_156 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_138, x_155, x_4, x_5, x_6, x_7, x_8, x_9, x_148);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_apply_8(x_142, x_157, x_4, x_5, x_6, x_7, x_8, x_9, x_158);
return x_159;
}
else
{
uint8_t x_160; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_146);
if (x_160 == 0)
{
return x_146;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_146, 0);
x_162 = lean_ctor_get(x_146, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_146);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_12);
if (x_164 == 0)
{
return x_12;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_12, 0);
x_166 = lean_ctor_get(x_12, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_12);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_hasMVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_st_ref_get(x_5, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instantiateMVarsCore(x_14, x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_5, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_17);
x_23 = lean_st_ref_set(x_5, x_19, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_19, 1);
x_29 = lean_ctor_get(x_19, 2);
x_30 = lean_ctor_get(x_19, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_st_ref_set(x_5, x_31, x_20);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", failed to discharge hypotheses", 32);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", failed to assign proof", 24);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_27; 
x_17 = lean_array_uget(x_4, x_6);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_17);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_7);
x_18 = x_34;
x_19 = x_14;
goto block_26;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_28, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_array_fget(x_30, x_31);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_31, x_41);
lean_dec(x_31);
lean_ctor_set(x_28, 1, x_42);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_43 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_BinderInfo_isInstImplicit(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_17);
x_47 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Expr_isMVar(x_48);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_44);
lean_dec(x_17);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_7);
x_18 = x_51;
x_19 = x_49;
goto block_26;
}
else
{
lean_object* x_52; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_44);
x_52 = l_Lean_Meta_isProp(x_44, x_10, x_11, x_12, x_13, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_44);
x_56 = l_Lean_Meta_isClass_x3f(x_44, x_10, x_11, x_12, x_13, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_44);
lean_dec(x_17);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_7);
x_18 = x_59;
x_19 = x_58;
goto block_26;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_57);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_61 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
lean_ctor_set(x_7, 0, x_65);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_7);
x_18 = x_66;
x_19 = x_64;
goto block_26;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_7);
x_18 = x_68;
x_19 = x_67;
goto block_26;
}
}
else
{
uint8_t x_69; 
lean_dec(x_28);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
return x_61;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_61, 0);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_61);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_52, 1);
lean_inc(x_73);
lean_dec(x_52);
lean_inc(x_2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_44);
x_74 = lean_apply_8(x_2, x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_free_object(x_7);
lean_dec(x_17);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_78 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_77, x_8, x_9, x_10, x_11, x_12, x_13, x_76);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_44);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_box(0);
x_83 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_28, x_82, x_8, x_9, x_10, x_11, x_12, x_13, x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_18 = x_84;
x_19 = x_85;
goto block_26;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
lean_dec(x_78);
lean_inc(x_1);
x_87 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
x_92 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__2;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_indentExpr(x_44);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
x_97 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_77, x_96, x_8, x_9, x_10, x_11, x_12, x_13, x_89);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_28, x_98, x_8, x_9, x_10, x_11, x_12, x_13, x_99);
lean_dec(x_98);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_18 = x_101;
x_19 = x_102;
goto block_26;
}
else
{
uint8_t x_103; 
lean_dec(x_44);
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_87);
if (x_103 == 0)
{
return x_87;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_87, 0);
x_105 = lean_ctor_get(x_87, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_87);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_74, 1);
lean_inc(x_107);
lean_dec(x_74);
x_108 = lean_ctor_get(x_75, 0);
lean_inc(x_108);
lean_dec(x_75);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_109 = l_Lean_Meta_isExprDefEq(x_17, x_108, x_10, x_11, x_12, x_13, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_free_object(x_7);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_114 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_113, x_8, x_9, x_10, x_11, x_12, x_13, x_112);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_44);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_box(0);
x_119 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_28, x_118, x_8, x_9, x_10, x_11, x_12, x_13, x_117);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_18 = x_120;
x_19 = x_121;
goto block_26;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_114, 1);
lean_inc(x_122);
lean_dec(x_114);
lean_inc(x_1);
x_123 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
x_128 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__4;
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_indentExpr(x_44);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_126);
x_133 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_113, x_132, x_8, x_9, x_10, x_11, x_12, x_13, x_125);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_28, x_134, x_8, x_9, x_10, x_11, x_12, x_13, x_135);
lean_dec(x_134);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_18 = x_137;
x_19 = x_138;
goto block_26;
}
else
{
uint8_t x_139; 
lean_dec(x_44);
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_123);
if (x_139 == 0)
{
return x_123;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_123, 0);
x_141 = lean_ctor_get(x_123, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_123);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_44);
x_143 = lean_ctor_get(x_109, 1);
lean_inc(x_143);
lean_dec(x_109);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_7);
x_18 = x_144;
x_19 = x_143;
goto block_26;
}
}
else
{
uint8_t x_145; 
lean_dec(x_44);
lean_dec(x_28);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_109);
if (x_145 == 0)
{
return x_109;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_109, 0);
x_147 = lean_ctor_get(x_109, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_109);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_44);
lean_dec(x_28);
lean_free_object(x_7);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_74);
if (x_149 == 0)
{
return x_74;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_74, 0);
x_151 = lean_ctor_get(x_74, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_74);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_44);
lean_dec(x_28);
lean_free_object(x_7);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_52);
if (x_153 == 0)
{
return x_52;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_52, 0);
x_155 = lean_ctor_get(x_52, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_52);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
lean_object* x_157; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_157 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_45);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
lean_ctor_set(x_7, 0, x_161);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_7);
x_18 = x_162;
x_19 = x_160;
goto block_26;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_dec(x_157);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_7);
x_18 = x_164;
x_19 = x_163;
goto block_26;
}
}
else
{
uint8_t x_165; 
lean_dec(x_28);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_157);
if (x_165 == 0)
{
return x_157;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_157, 0);
x_167 = lean_ctor_get(x_157, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_157);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_28);
lean_free_object(x_7);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_43);
if (x_169 == 0)
{
return x_43;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_43, 0);
x_171 = lean_ctor_get(x_43, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_43);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_28);
x_173 = lean_array_fget(x_30, x_31);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_add(x_31, x_175);
lean_dec(x_31);
x_177 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_177, 0, x_30);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_32);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_178 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = l_Lean_BinderInfo_isInstImplicit(x_174);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_inc(x_17);
x_182 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_180);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lean_Expr_isMVar(x_183);
lean_dec(x_183);
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec(x_179);
lean_dec(x_17);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_177);
lean_ctor_set(x_7, 0, x_3);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_7);
x_18 = x_186;
x_19 = x_184;
goto block_26;
}
else
{
lean_object* x_187; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_179);
x_187 = l_Lean_Meta_isProp(x_179, x_10, x_11, x_12, x_13, x_184);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_179);
x_191 = l_Lean_Meta_isClass_x3f(x_179, x_10, x_11, x_12, x_13, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_179);
lean_dec(x_17);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_177);
lean_ctor_set(x_7, 0, x_3);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_7);
x_18 = x_194;
x_19 = x_193;
goto block_26;
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_192);
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_dec(x_191);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_196 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_179, x_8, x_9, x_10, x_11, x_12, x_13, x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; uint8_t x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_unbox(x_197);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
lean_ctor_set(x_7, 1, x_177);
lean_ctor_set(x_7, 0, x_200);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_7);
x_18 = x_201;
x_19 = x_199;
goto block_26;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
lean_dec(x_196);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_177);
lean_ctor_set(x_7, 0, x_3);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_7);
x_18 = x_203;
x_19 = x_202;
goto block_26;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_177);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_ctor_get(x_196, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_196, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_206 = x_196;
} else {
 lean_dec_ref(x_196);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_187, 1);
lean_inc(x_208);
lean_dec(x_187);
lean_inc(x_2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_179);
x_209 = lean_apply_8(x_2, x_179, x_8, x_9, x_10, x_11, x_12, x_13, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
lean_free_object(x_7);
lean_dec(x_17);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_213 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_212, x_8, x_9, x_10, x_11, x_12, x_13, x_211);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_unbox(x_214);
lean_dec(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_179);
x_216 = lean_ctor_get(x_213, 1);
lean_inc(x_216);
lean_dec(x_213);
x_217 = lean_box(0);
x_218 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_177, x_217, x_8, x_9, x_10, x_11, x_12, x_13, x_216);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_18 = x_219;
x_19 = x_220;
goto block_26;
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_213, 1);
lean_inc(x_221);
lean_dec(x_213);
lean_inc(x_1);
x_222 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_223);
x_227 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__2;
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Lean_indentExpr(x_179);
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_225);
x_232 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_212, x_231, x_8, x_9, x_10, x_11, x_12, x_13, x_224);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_177, x_233, x_8, x_9, x_10, x_11, x_12, x_13, x_234);
lean_dec(x_233);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_18 = x_236;
x_19 = x_237;
goto block_26;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = lean_ctor_get(x_222, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_222, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_240 = x_222;
} else {
 lean_dec_ref(x_222);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_209, 1);
lean_inc(x_242);
lean_dec(x_209);
x_243 = lean_ctor_get(x_210, 0);
lean_inc(x_243);
lean_dec(x_210);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_244 = l_Lean_Meta_isExprDefEq(x_17, x_243, x_10, x_11, x_12, x_13, x_242);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_unbox(x_245);
lean_dec(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
lean_free_object(x_7);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
lean_dec(x_244);
x_248 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_249 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_248, x_8, x_9, x_10, x_11, x_12, x_13, x_247);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_unbox(x_250);
lean_dec(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_179);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
lean_dec(x_249);
x_253 = lean_box(0);
x_254 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_177, x_253, x_8, x_9, x_10, x_11, x_12, x_13, x_252);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_18 = x_255;
x_19 = x_256;
goto block_26;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_249, 1);
lean_inc(x_257);
lean_dec(x_249);
lean_inc(x_1);
x_258 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_257);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_262 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_259);
x_263 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__4;
x_264 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_Lean_indentExpr(x_179);
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_261);
x_268 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_248, x_267, x_8, x_9, x_10, x_11, x_12, x_13, x_260);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_177, x_269, x_8, x_9, x_10, x_11, x_12, x_13, x_270);
lean_dec(x_269);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_18 = x_272;
x_19 = x_273;
goto block_26;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_179);
lean_dec(x_177);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_274 = lean_ctor_get(x_258, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_258, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_276 = x_258;
} else {
 lean_dec_ref(x_258);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_179);
x_278 = lean_ctor_get(x_244, 1);
lean_inc(x_278);
lean_dec(x_244);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_177);
lean_ctor_set(x_7, 0, x_3);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_7);
x_18 = x_279;
x_19 = x_278;
goto block_26;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_179);
lean_dec(x_177);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_280 = lean_ctor_get(x_244, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_244, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_282 = x_244;
} else {
 lean_dec_ref(x_244);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_179);
lean_dec(x_177);
lean_free_object(x_7);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_284 = lean_ctor_get(x_209, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_209, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_286 = x_209;
} else {
 lean_dec_ref(x_209);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_179);
lean_dec(x_177);
lean_free_object(x_7);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_288 = lean_ctor_get(x_187, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_187, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_290 = x_187;
} else {
 lean_dec_ref(x_187);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
}
else
{
lean_object* x_292; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_292 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_179, x_8, x_9, x_10, x_11, x_12, x_13, x_180);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; uint8_t x_294; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_unbox(x_293);
lean_dec(x_293);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_292, 1);
lean_inc(x_295);
lean_dec(x_292);
x_296 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
lean_ctor_set(x_7, 1, x_177);
lean_ctor_set(x_7, 0, x_296);
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_7);
x_18 = x_297;
x_19 = x_295;
goto block_26;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_292, 1);
lean_inc(x_298);
lean_dec(x_292);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_177);
lean_ctor_set(x_7, 0, x_3);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_7);
x_18 = x_299;
x_19 = x_298;
goto block_26;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_177);
lean_free_object(x_7);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_300 = lean_ctor_get(x_292, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_292, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_302 = x_292;
} else {
 lean_dec_ref(x_292);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_177);
lean_free_object(x_7);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_304 = lean_ctor_get(x_178, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_178, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_306 = x_178;
} else {
 lean_dec_ref(x_178);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_308 = lean_ctor_get(x_7, 1);
lean_inc(x_308);
lean_dec(x_7);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_308, 2);
lean_inc(x_311);
x_312 = lean_nat_dec_lt(x_310, x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_17);
lean_inc(x_3);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_3);
lean_ctor_set(x_313, 1, x_308);
x_314 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_314, 0, x_313);
x_18 = x_314;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 lean_ctor_release(x_308, 2);
 x_315 = x_308;
} else {
 lean_dec_ref(x_308);
 x_315 = lean_box(0);
}
x_316 = lean_array_fget(x_309, x_310);
x_317 = lean_unbox(x_316);
lean_dec(x_316);
x_318 = lean_unsigned_to_nat(1u);
x_319 = lean_nat_add(x_310, x_318);
lean_dec(x_310);
if (lean_is_scalar(x_315)) {
 x_320 = lean_alloc_ctor(0, 3, 0);
} else {
 x_320 = x_315;
}
lean_ctor_set(x_320, 0, x_309);
lean_ctor_set(x_320, 1, x_319);
lean_ctor_set(x_320, 2, x_311);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_321 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = l_Lean_BinderInfo_isInstImplicit(x_317);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
lean_inc(x_17);
x_325 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_323);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_328 = l_Lean_Expr_isMVar(x_326);
lean_dec(x_326);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_322);
lean_dec(x_17);
lean_inc(x_3);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_3);
lean_ctor_set(x_329, 1, x_320);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_329);
x_18 = x_330;
x_19 = x_327;
goto block_26;
}
else
{
lean_object* x_331; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_322);
x_331 = l_Lean_Meta_isProp(x_322, x_10, x_11, x_12, x_13, x_327);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; uint8_t x_333; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_unbox(x_332);
lean_dec(x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_331, 1);
lean_inc(x_334);
lean_dec(x_331);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_322);
x_335 = l_Lean_Meta_isClass_x3f(x_322, x_10, x_11, x_12, x_13, x_334);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_322);
lean_dec(x_17);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
lean_inc(x_3);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_3);
lean_ctor_set(x_338, 1, x_320);
x_339 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_339, 0, x_338);
x_18 = x_339;
x_19 = x_337;
goto block_26;
}
else
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_336);
x_340 = lean_ctor_get(x_335, 1);
lean_inc(x_340);
lean_dec(x_335);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_341 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_322, x_8, x_9, x_10, x_11, x_12, x_13, x_340);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; uint8_t x_343; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_unbox(x_342);
lean_dec(x_342);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_344 = lean_ctor_get(x_341, 1);
lean_inc(x_344);
lean_dec(x_341);
x_345 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_320);
x_347 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_347, 0, x_346);
x_18 = x_347;
x_19 = x_344;
goto block_26;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_341, 1);
lean_inc(x_348);
lean_dec(x_341);
lean_inc(x_3);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_3);
lean_ctor_set(x_349, 1, x_320);
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_349);
x_18 = x_350;
x_19 = x_348;
goto block_26;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_320);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_351 = lean_ctor_get(x_341, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_341, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_353 = x_341;
} else {
 lean_dec_ref(x_341);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_331, 1);
lean_inc(x_355);
lean_dec(x_331);
lean_inc(x_2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_322);
x_356 = lean_apply_8(x_2, x_322, x_8, x_9, x_10, x_11, x_12, x_13, x_355);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
lean_dec(x_17);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_360 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_359, x_8, x_9, x_10, x_11, x_12, x_13, x_358);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_unbox(x_361);
lean_dec(x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_322);
x_363 = lean_ctor_get(x_360, 1);
lean_inc(x_363);
lean_dec(x_360);
x_364 = lean_box(0);
x_365 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_320, x_364, x_8, x_9, x_10, x_11, x_12, x_13, x_363);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_18 = x_366;
x_19 = x_367;
goto block_26;
}
else
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_360, 1);
lean_inc(x_368);
lean_dec(x_360);
lean_inc(x_1);
x_369 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_373 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_370);
x_374 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__2;
x_375 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
x_376 = l_Lean_indentExpr(x_322);
x_377 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_372);
x_379 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_359, x_378, x_8, x_9, x_10, x_11, x_12, x_13, x_371);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_382 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_320, x_380, x_8, x_9, x_10, x_11, x_12, x_13, x_381);
lean_dec(x_380);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
lean_dec(x_382);
x_18 = x_383;
x_19 = x_384;
goto block_26;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_322);
lean_dec(x_320);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_385 = lean_ctor_get(x_369, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_369, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_387 = x_369;
} else {
 lean_dec_ref(x_369);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_356, 1);
lean_inc(x_389);
lean_dec(x_356);
x_390 = lean_ctor_get(x_357, 0);
lean_inc(x_390);
lean_dec(x_357);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_391 = l_Lean_Meta_isExprDefEq(x_17, x_390, x_10, x_11, x_12, x_13, x_389);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; uint8_t x_393; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_unbox(x_392);
lean_dec(x_392);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_394 = lean_ctor_get(x_391, 1);
lean_inc(x_394);
lean_dec(x_391);
x_395 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_396 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_395, x_8, x_9, x_10, x_11, x_12, x_13, x_394);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_unbox(x_397);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_322);
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_dec(x_396);
x_400 = lean_box(0);
x_401 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_320, x_400, x_8, x_9, x_10, x_11, x_12, x_13, x_399);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_18 = x_402;
x_19 = x_403;
goto block_26;
}
else
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_396, 1);
lean_inc(x_404);
lean_dec(x_396);
lean_inc(x_1);
x_405 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_404);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_409 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_406);
x_410 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__4;
x_411 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_indentExpr(x_322);
x_413 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
x_414 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_408);
x_415 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_395, x_414, x_8, x_9, x_10, x_11, x_12, x_13, x_407);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_418 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_320, x_416, x_8, x_9, x_10, x_11, x_12, x_13, x_417);
lean_dec(x_416);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_18 = x_419;
x_19 = x_420;
goto block_26;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_322);
lean_dec(x_320);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_421 = lean_ctor_get(x_405, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_405, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_423 = x_405;
} else {
 lean_dec_ref(x_405);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_421);
lean_ctor_set(x_424, 1, x_422);
return x_424;
}
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_322);
x_425 = lean_ctor_get(x_391, 1);
lean_inc(x_425);
lean_dec(x_391);
lean_inc(x_3);
x_426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_426, 0, x_3);
lean_ctor_set(x_426, 1, x_320);
x_427 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_427, 0, x_426);
x_18 = x_427;
x_19 = x_425;
goto block_26;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_322);
lean_dec(x_320);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_428 = lean_ctor_get(x_391, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_391, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_430 = x_391;
} else {
 lean_dec_ref(x_391);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_428);
lean_ctor_set(x_431, 1, x_429);
return x_431;
}
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_322);
lean_dec(x_320);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_432 = lean_ctor_get(x_356, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_356, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_434 = x_356;
} else {
 lean_dec_ref(x_356);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 2, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_433);
return x_435;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_322);
lean_dec(x_320);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_436 = lean_ctor_get(x_331, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_331, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_438 = x_331;
} else {
 lean_dec_ref(x_331);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
}
else
{
lean_object* x_440; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_440 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_322, x_8, x_9, x_10, x_11, x_12, x_13, x_323);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; uint8_t x_442; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_unbox(x_441);
lean_dec(x_441);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_443 = lean_ctor_get(x_440, 1);
lean_inc(x_443);
lean_dec(x_440);
x_444 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_320);
x_446 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_446, 0, x_445);
x_18 = x_446;
x_19 = x_443;
goto block_26;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_440, 1);
lean_inc(x_447);
lean_dec(x_440);
lean_inc(x_3);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_3);
lean_ctor_set(x_448, 1, x_320);
x_449 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_449, 0, x_448);
x_18 = x_449;
x_19 = x_447;
goto block_26;
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_320);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_450 = lean_ctor_get(x_440, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_440, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_452 = x_440;
} else {
 lean_dec_ref(x_440);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 2, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_450);
lean_ctor_set(x_453, 1, x_451);
return x_453;
}
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_320);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_454 = lean_ctor_get(x_321, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_321, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_456 = x_321;
} else {
 lean_dec_ref(x_321);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_455);
return x_457;
}
}
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_6, x_23);
x_6 = x_24;
x_7 = x_22;
x_14 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_synthesizeArgs___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_toSubarray___rarg(x_3, x_13, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_get_size(x_2);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(x_1, x_4, x_15, x_2, x_18, x_19, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Meta_Simp_synthesizeArgs___closed__1;
x_25 = lean_box(0);
x_26 = lean_apply_8(x_24, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_synthesizeArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_synthesizeArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":perm", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Nat_repr(x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Nat_repr(x_27);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 4);
lean_inc(x_43);
x_44 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Nat_repr(x_47);
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_44, 0, x_57);
return x_44;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = lean_ctor_get(x_1, 3);
lean_inc(x_60);
lean_dec(x_1);
x_61 = l_Nat_repr(x_60);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_59);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_44);
if (x_72 == 0)
{
return x_44;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_44, 0);
x_74 = lean_ctor_get(x_44, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_44);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
x_13 = l_Lean_MetavarContext_getDecl(x_12, x_1);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_box(x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_20);
x_21 = l_Lean_MetavarContext_getDecl(x_20, x_1);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2;
x_2 = l_instInhabitedBool;
x_3 = lean_box(x_2);
x_4 = l_instInhabited___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.MetavarContext", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.isLevelMVarAssignable", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown universe metavariable", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1;
x_2 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2;
x_3 = lean_unsigned_to_nat(393u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_free_object(x_9);
x_16 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4;
x_17 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_nat_dec_le(x_19, x_18);
lean_dec(x_18);
lean_dec(x_19);
x_21 = lean_box(x_20);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
x_26 = l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
x_27 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4;
x_28 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_dec_le(x_30, x_29);
lean_dec(x_29);
lean_dec(x_30);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Level_hasMVar(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
x_1 = x_9;
goto _start;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Level_hasMVar(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = l_Lean_Level_hasMVar(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
else
{
x_1 = x_15;
goto _start;
}
}
else
{
lean_object* x_21; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_22);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_21, 0);
lean_dec(x_26);
x_27 = l_Lean_Level_hasMVar(x_15);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_box(x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_free_object(x_21);
x_1 = x_15;
x_8 = x_25;
goto _start;
}
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = l_Lean_Level_hasMVar(x_15);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
x_1 = x_15;
x_8 = x_30;
goto _start;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_21, 0);
lean_dec(x_36);
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_22);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
case 3:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lean_Level_hasMVar(x_43);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_43);
x_46 = l_Lean_Level_hasMVar(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_8);
return x_48;
}
else
{
x_1 = x_44;
goto _start;
}
}
else
{
lean_object* x_50; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_50 = l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
if (x_52 == 0)
{
uint8_t x_53; 
lean_dec(x_51);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_50, 1);
x_55 = lean_ctor_get(x_50, 0);
lean_dec(x_55);
x_56 = l_Lean_Level_hasMVar(x_44);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_box(x_56);
lean_ctor_set(x_50, 0, x_57);
return x_50;
}
else
{
lean_free_object(x_50);
x_1 = x_44;
x_8 = x_54;
goto _start;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_dec(x_50);
x_60 = l_Lean_Level_hasMVar(x_44);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
x_1 = x_44;
x_8 = x_59;
goto _start;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_50);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_50, 0);
lean_dec(x_65);
return x_50;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_dec(x_50);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_51);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_50);
if (x_68 == 0)
{
return x_50;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_50, 0);
x_70 = lean_ctor_get(x_50, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_50);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
case 5:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
lean_dec(x_1);
x_73 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_73;
}
default: 
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = 0;
x_75 = lean_box(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_8);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_1 = x_13;
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
case 4:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_List_anyM___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__7(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
case 5:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Expr_hasMVar(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
x_1 = x_16;
goto _start;
}
}
else
{
lean_object* x_22; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_23);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_22, 0);
lean_dec(x_27);
x_28 = l_Lean_Expr_hasMVar(x_16);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(x_28);
lean_ctor_set(x_22, 0, x_29);
return x_22;
}
else
{
lean_free_object(x_22);
x_1 = x_16;
x_8 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l_Lean_Expr_hasMVar(x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
x_1 = x_16;
x_8 = x_31;
goto _start;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_22, 0);
lean_dec(x_37);
return x_22;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
return x_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_22, 0);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
case 6:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_Expr_hasMVar(x_44);
if (x_46 == 0)
{
uint8_t x_47; 
lean_dec(x_44);
x_47 = l_Lean_Expr_hasMVar(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_8);
return x_49;
}
else
{
x_1 = x_45;
goto _start;
}
}
else
{
lean_object* x_51; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_51 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec(x_52);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_51, 1);
x_56 = lean_ctor_get(x_51, 0);
lean_dec(x_56);
x_57 = l_Lean_Expr_hasMVar(x_45);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_box(x_57);
lean_ctor_set(x_51, 0, x_58);
return x_51;
}
else
{
lean_free_object(x_51);
x_1 = x_45;
x_8 = x_55;
goto _start;
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_dec(x_51);
x_61 = l_Lean_Expr_hasMVar(x_45);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
x_1 = x_45;
x_8 = x_60;
goto _start;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_51);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_51, 0);
lean_dec(x_66);
return x_51;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_51, 1);
lean_inc(x_67);
lean_dec(x_51);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_52);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_51);
if (x_69 == 0)
{
return x_51;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_51, 0);
x_71 = lean_ctor_get(x_51, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_51);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
case 7:
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 2);
lean_inc(x_74);
lean_dec(x_1);
x_75 = l_Lean_Expr_hasMVar(x_73);
if (x_75 == 0)
{
uint8_t x_76; 
lean_dec(x_73);
x_76 = l_Lean_Expr_hasMVar(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_box(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_8);
return x_78;
}
else
{
x_1 = x_74;
goto _start;
}
}
else
{
lean_object* x_80; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_80 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
if (x_82 == 0)
{
uint8_t x_83; 
lean_dec(x_81);
x_83 = !lean_is_exclusive(x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_80, 1);
x_85 = lean_ctor_get(x_80, 0);
lean_dec(x_85);
x_86 = l_Lean_Expr_hasMVar(x_74);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_box(x_86);
lean_ctor_set(x_80, 0, x_87);
return x_80;
}
else
{
lean_free_object(x_80);
x_1 = x_74;
x_8 = x_84;
goto _start;
}
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
lean_dec(x_80);
x_90 = l_Lean_Expr_hasMVar(x_74);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_box(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
x_1 = x_74;
x_8 = x_89;
goto _start;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_80);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_80, 0);
lean_dec(x_95);
return x_80;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_80, 1);
lean_inc(x_96);
lean_dec(x_80);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_81);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_74);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_80);
if (x_98 == 0)
{
return x_80;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_80, 0);
x_100 = lean_ctor_get(x_80, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_80);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
case 8:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = lean_ctor_get(x_1, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_1, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_1, 3);
lean_inc(x_104);
lean_dec(x_1);
x_105 = l_Lean_Expr_hasMVar(x_102);
if (x_105 == 0)
{
uint8_t x_106; 
lean_dec(x_102);
x_106 = l_Lean_Expr_hasMVar(x_103);
if (x_106 == 0)
{
uint8_t x_107; 
lean_dec(x_103);
x_107 = l_Lean_Expr_hasMVar(x_104);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_box(x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_8);
return x_109;
}
else
{
x_1 = x_104;
goto _start;
}
}
else
{
lean_object* x_111; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_111 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_unbox(x_112);
if (x_113 == 0)
{
uint8_t x_114; 
lean_dec(x_112);
x_114 = !lean_is_exclusive(x_111);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_111, 1);
x_116 = lean_ctor_get(x_111, 0);
lean_dec(x_116);
x_117 = l_Lean_Expr_hasMVar(x_104);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_118 = lean_box(x_117);
lean_ctor_set(x_111, 0, x_118);
return x_111;
}
else
{
lean_free_object(x_111);
x_1 = x_104;
x_8 = x_115;
goto _start;
}
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
lean_dec(x_111);
x_121 = l_Lean_Expr_hasMVar(x_104);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_box(x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
else
{
x_1 = x_104;
x_8 = x_120;
goto _start;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = !lean_is_exclusive(x_111);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_111, 0);
lean_dec(x_126);
return x_111;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_111, 1);
lean_inc(x_127);
lean_dec(x_111);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_112);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_111);
if (x_129 == 0)
{
return x_111;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_111, 0);
x_131 = lean_ctor_get(x_111, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_111);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
lean_object* x_133; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_133 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_unbox(x_134);
if (x_135 == 0)
{
uint8_t x_136; 
lean_dec(x_134);
x_136 = !lean_is_exclusive(x_133);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_133, 1);
x_138 = lean_ctor_get(x_133, 0);
lean_dec(x_138);
x_139 = l_Lean_Expr_hasMVar(x_103);
if (x_139 == 0)
{
uint8_t x_140; 
lean_dec(x_103);
x_140 = l_Lean_Expr_hasMVar(x_104);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = lean_box(x_140);
lean_ctor_set(x_133, 0, x_141);
return x_133;
}
else
{
lean_free_object(x_133);
x_1 = x_104;
x_8 = x_137;
goto _start;
}
}
else
{
lean_object* x_143; 
lean_free_object(x_133);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_143 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_137);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
if (x_145 == 0)
{
uint8_t x_146; 
lean_dec(x_144);
x_146 = !lean_is_exclusive(x_143);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_143, 1);
x_148 = lean_ctor_get(x_143, 0);
lean_dec(x_148);
x_149 = l_Lean_Expr_hasMVar(x_104);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_150 = lean_box(x_149);
lean_ctor_set(x_143, 0, x_150);
return x_143;
}
else
{
lean_free_object(x_143);
x_1 = x_104;
x_8 = x_147;
goto _start;
}
}
else
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_143, 1);
lean_inc(x_152);
lean_dec(x_143);
x_153 = l_Lean_Expr_hasMVar(x_104);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_154 = lean_box(x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_152);
return x_155;
}
else
{
x_1 = x_104;
x_8 = x_152;
goto _start;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_143);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_143, 0);
lean_dec(x_158);
return x_143;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_143, 1);
lean_inc(x_159);
lean_dec(x_143);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_144);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_161 = !lean_is_exclusive(x_143);
if (x_161 == 0)
{
return x_143;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_143, 0);
x_163 = lean_ctor_get(x_143, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_143);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
else
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_133, 1);
lean_inc(x_165);
lean_dec(x_133);
x_166 = l_Lean_Expr_hasMVar(x_103);
if (x_166 == 0)
{
uint8_t x_167; 
lean_dec(x_103);
x_167 = l_Lean_Expr_hasMVar(x_104);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_168 = lean_box(x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_165);
return x_169;
}
else
{
x_1 = x_104;
x_8 = x_165;
goto _start;
}
}
else
{
lean_object* x_171; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_171 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_165);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
lean_dec(x_172);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_175 = x_171;
} else {
 lean_dec_ref(x_171);
 x_175 = lean_box(0);
}
x_176 = l_Lean_Expr_hasMVar(x_104);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_177 = lean_box(x_176);
if (lean_is_scalar(x_175)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_175;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_174);
return x_178;
}
else
{
lean_dec(x_175);
x_1 = x_104;
x_8 = x_174;
goto _start;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = lean_ctor_get(x_171, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_181 = x_171;
} else {
 lean_dec_ref(x_171);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_172);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_183 = lean_ctor_get(x_171, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_171, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_185 = x_171;
} else {
 lean_dec_ref(x_171);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_187 = !lean_is_exclusive(x_133);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_133, 0);
lean_dec(x_188);
return x_133;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_133, 1);
lean_inc(x_189);
lean_dec(x_133);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_134);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_191 = !lean_is_exclusive(x_133);
if (x_191 == 0)
{
return x_133;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_133, 0);
x_193 = lean_ctor_get(x_133, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_133);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
case 10:
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_ctor_get(x_1, 1);
lean_inc(x_195);
lean_dec(x_1);
x_196 = l_Lean_Expr_hasMVar(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_195);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = lean_box(x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_8);
return x_198;
}
else
{
x_1 = x_195;
goto _start;
}
}
case 11:
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_ctor_get(x_1, 2);
lean_inc(x_200);
lean_dec(x_1);
x_201 = l_Lean_Expr_hasMVar(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_200);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_202 = lean_box(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_8);
return x_203;
}
else
{
x_1 = x_200;
goto _start;
}
}
default: 
{
uint8_t x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = 0;
x_206 = lean_box(x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_8);
return x_207;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Meta_Simp_recordSimpTheorem(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rewrite", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
x_2 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
x_3 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
x_4 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ==> ", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(x_1, x_2, x_3, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofExpr(x_5);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_2);
x_33 = l_Lean_MessageData_ofExpr(x_2);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
x_36 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_14, x_35, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(x_1, x_2, x_3, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_38);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_37);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
return x_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_22, 0);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", perm rejected ", 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
lean_dec(x_6);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; 
x_17 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_2);
x_18 = l_Lean_Meta_ACLt_main_lt(x_17, x_2, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
x_23 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_27 = lean_unbox(x_24);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = lean_apply_8(x_26, x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_MessageData_ofExpr(x_5);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_MessageData_ofExpr(x_2);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
x_44 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_22, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_apply_8(x_26, x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_dec(x_18);
x_53 = lean_box(0);
x_54 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(x_1, x_2, x_3, x_4, x_5, x_53, x_7, x_8, x_9, x_10, x_11, x_12, x_52);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_18);
if (x_55 == 0)
{
return x_18;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = lean_ctor_get(x_18, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_18);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_18 = lean_expr_eqv(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4(x_2, x_17, x_5, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_25 = lean_expr_eqv(x_4, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4(x_2, x_24, x_5, x_3, x_4, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_apply_8(x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", has unassigned metavariables after unification", 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
lean_dec(x_7);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*5 + 2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_3);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__5), 12, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
x_17 = l_Lean_mkAppN(x_5, x_6);
x_18 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_19);
x_21 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6(x_19, x_16, x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_19);
lean_dec(x_16);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
x_29 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_33 = lean_unbox(x_30);
lean_dec(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = lean_apply_8(x_32, x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_28, x_42, x_8, x_9, x_10, x_11, x_12, x_13, x_38);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_apply_8(x_32, x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_45);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
return x_21;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_21, 0);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_21);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_6);
lean_dec(x_5);
x_55 = lean_box(0);
x_56 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__5(x_1, x_2, x_3, x_4, x_55, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_56;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unify", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
x_2 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
x_3 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
x_4 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", failed to unify", 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nwith", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_16 = l_Lean_Meta_isExprDefEq(x_1, x_8, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_21 = l_Lean_Expr_isMVar(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2;
x_23 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = lean_apply_8(x_20, x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_indentExpr(x_1);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_indentExpr(x_8);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
x_44 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_22, x_43, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_apply_8(x_20, x_45, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_apply_8(x_20, x_52, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_54 = lean_ctor_get(x_16, 1);
lean_inc(x_54);
lean_dec(x_16);
x_55 = lean_ctor_get(x_6, 4);
lean_inc(x_55);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_55);
x_56 = l_Lean_Meta_Simp_synthesizeArgs(x_55, x_2, x_3, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_55);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_56, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_56, 0, x_61);
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_dec(x_56);
x_66 = lean_box(0);
x_67 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7(x_5, x_55, x_6, x_8, x_4, x_2, x_66, x_9, x_10, x_11, x_12, x_13, x_14, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_55);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_56);
if (x_68 == 0)
{
return x_56;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_56, 0);
x_70 = lean_ctor_get(x_56, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_56);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_16);
if (x_72 == 0)
{
return x_16;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_16, 0);
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_16);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_1, x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_Lean_Expr_appArg_x21(x_18);
x_21 = lean_array_push(x_19, x_20);
x_22 = l_Lean_Expr_appFn_x21(x_18);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_17;
x_2 = x_24;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_mkCongrFun(x_4, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_16;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_mkAppN(x_1, x_2);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lean_mkAppN(x_1, x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", resulting expression has unassigned metavariables", 51);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_21 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__1(x_8, x_19, x_8, x_20, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Array_reverse___rarg(x_25);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_27 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(x_1, x_2, x_3, x_4, x_5, x_7, x_9, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_38);
x_39 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_38, x_10, x_11, x_12, x_13, x_14, x_15, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_7);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1(x_38, x_26, x_43, x_10, x_11, x_12, x_13, x_14, x_15, x_42);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_38);
lean_dec(x_26);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
x_47 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_46, x_10, x_11, x_12, x_13, x_14, x_15, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
x_62 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_46, x_63, x_10, x_11, x_12, x_13, x_14, x_15, x_59);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_71 = !lean_is_exclusive(x_57);
if (x_71 == 0)
{
return x_57;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_57, 0);
x_73 = lean_ctor_get(x_57, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_57);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_75 = !lean_is_exclusive(x_39);
if (x_75 == 0)
{
return x_39;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_39, 0);
x_77 = lean_ctor_get(x_39, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_39);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_27, 1);
lean_inc(x_79);
lean_dec(x_27);
x_80 = lean_ctor_get(x_35, 0);
lean_inc(x_80);
lean_dec(x_35);
x_81 = lean_ctor_get(x_36, 0);
lean_inc(x_81);
lean_dec(x_36);
x_82 = lean_array_get_size(x_26);
x_83 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_84 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_85 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__2(x_26, x_83, x_84, x_81, x_10, x_11, x_12, x_13, x_14, x_15, x_79);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_80);
x_88 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_80, x_10, x_11, x_12, x_13, x_14, x_15, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_7);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_box(0);
x_93 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__2(x_80, x_26, x_86, x_92, x_10, x_11, x_12, x_13, x_14, x_15, x_91);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_86);
lean_dec(x_80);
lean_dec(x_26);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_dec(x_88);
x_95 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
x_96 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_95, x_10, x_11, x_12, x_13, x_14, x_15, x_94);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
uint8_t x_99; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_99 = !lean_is_exclusive(x_96);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_96, 0);
lean_dec(x_100);
x_101 = lean_box(0);
lean_ctor_set(x_96, 0, x_101);
return x_96;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_dec(x_96);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_96, 1);
lean_inc(x_105);
lean_dec(x_96);
x_106 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
x_111 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_95, x_112, x_10, x_11, x_12, x_13, x_14, x_15, x_108);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_113, 0);
lean_dec(x_115);
x_116 = lean_box(0);
lean_ctor_set(x_113, 0, x_116);
return x_113;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
lean_dec(x_113);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_120 = !lean_is_exclusive(x_106);
if (x_120 == 0)
{
return x_106;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_106, 0);
x_122 = lean_ctor_get(x_106, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_106);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_86);
lean_dec(x_80);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_124 = !lean_is_exclusive(x_88);
if (x_124 == 0)
{
return x_88;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_88, 0);
x_126 = lean_ctor_get(x_88, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_88);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_80);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_128 = !lean_is_exclusive(x_85);
if (x_128 == 0)
{
return x_85;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_85, 0);
x_130 = lean_ctor_get(x_85, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_85);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_132 = !lean_is_exclusive(x_27);
if (x_132 == 0)
{
return x_27;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_27, 0);
x_134 = lean_ctor_get(x_27, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_27);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_8(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_1, x_3, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(x_2, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SimpTheorem_getValue(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_13 = lean_infer_type(x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = 1;
x_18 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_14, x_17, x_16, x_18, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = lean_whnf(x_27, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_appFn_x21(x_30);
x_33 = l_Lean_Expr_appArg_x21(x_32);
lean_dec(x_32);
x_34 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_33, x_23, x_24, x_5, x_30, x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
return x_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed), 8, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__2), 12, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg), 9, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = 0;
x_16 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_12 = lean_infer_type(x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = 1;
x_17 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_13, x_16, x_15, x_17, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = lean_whnf(x_26, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Expr_appFn_x21(x_29);
x_32 = l_Lean_Expr_appArg_x21(x_31);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_29);
lean_inc(x_4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_32);
x_34 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_32, x_22, x_23, x_4, x_29, x_1, x_2, x_33, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_32, x_33);
x_40 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_33);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_34, 0, x_15);
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_34);
x_42 = lean_nat_sub(x_40, x_39);
lean_dec(x_39);
lean_dec(x_40);
x_43 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_32, x_22, x_23, x_4, x_29, x_1, x_2, x_42, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_32, x_33);
x_46 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_33);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_15);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_sub(x_46, x_45);
lean_dec(x_45);
lean_dec(x_46);
x_50 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_32, x_22, x_23, x_4, x_29, x_1, x_2, x_49, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_34);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_34, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_35);
if (x_53 == 0)
{
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_35, 0);
lean_inc(x_54);
lean_dec(x_35);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_34, 0, x_55);
return x_34;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_dec(x_34);
x_57 = lean_ctor_get(x_35, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_58 = x_35;
} else {
 lean_dec_ref(x_35);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_34);
if (x_61 == 0)
{
return x_34;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_34, 0);
x_63 = lean_ctor_get(x_34, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_34);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_28);
if (x_65 == 0)
{
return x_28;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_28, 0);
x_67 = lean_ctor_get(x_28, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_28);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_18);
if (x_69 == 0)
{
return x_18;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_18, 0);
x_71 = lean_ctor_get(x_18, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_18);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
return x_12;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_12, 0);
x_75 = lean_ctor_get(x_12, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_12);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed), 8, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheorem_x3f___lambda__1), 11, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg), 9, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = 0;
x_15 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_isLemma___spec__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_inErasedSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Simp_rewrite_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_array_fget(x_1, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_nat_dec_lt(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_15; 
x_15 = lean_array_fswap(x_1, x_2, x_7);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_7;
x_3 = lean_box(0);
goto _start;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_10 = l_Array_insertionSort_swapLoop___at_Lean_Meta_Simp_rewrite_x3f___spec__2(x_1, x_2, lean_box(0));
x_11 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
x_3 = x_7;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Debug", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1;
x_2 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
x_3 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
x_4 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rewrite result ", 15);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" => ", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_8, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_69; 
lean_dec(x_9);
x_19 = lean_array_uget(x_6, x_8);
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
lean_inc(x_29);
lean_inc(x_2);
x_69 = l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(x_2, x_29);
if (x_69 == 0)
{
if (x_4 == 0)
{
lean_object* x_70; 
x_70 = lean_box(0);
x_31 = x_70;
goto block_68;
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_29, sizeof(void*)*5 + 2);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_30);
lean_dec(x_29);
lean_inc(x_5);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_5);
x_20 = x_72;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_73; 
x_73 = lean_box(0);
x_31 = x_73;
goto block_68;
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_30);
lean_dec(x_29);
lean_inc(x_5);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_5);
x_20 = x_74;
x_21 = x_16;
goto block_28;
}
block_28:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = 1;
x_26 = lean_usize_add(x_8, x_25);
x_8 = x_26;
x_9 = x_24;
x_16 = x_21;
goto _start;
}
}
block_68:
{
lean_object* x_32; 
lean_dec(x_31);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_1);
x_32 = l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(x_1, x_29, x_30, x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_5);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_5);
x_20 = x_35;
x_21 = x_34;
goto block_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2;
x_39 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_38, x_10, x_11, x_12, x_13, x_14, x_15, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(x_37, x_43, x_10, x_11, x_12, x_13, x_14, x_15, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_20 = x_45;
x_21 = x_46;
goto block_28;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
lean_inc(x_1);
x_48 = l_Lean_MessageData_ofExpr(x_1);
x_49 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_ctor_get(x_37, 0);
lean_inc(x_53);
x_54 = l_Lean_MessageData_ofExpr(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_38, x_57, x_10, x_11, x_12, x_13, x_14, x_15, x_47);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(x_37, x_59, x_10, x_11, x_12, x_13, x_14, x_15, x_60);
lean_dec(x_59);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_20 = x_62;
x_21 = x_63;
goto block_28;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
return x_32;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_32, 0);
x_66 = lean_ctor_get(x_32, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_32);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("no theorems found for ", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_rewrite_x3f___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-rewriting ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_rewrite_x3f___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_15 = l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(x_14, x_2, x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Array_isEmpty___rarg(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_array_get_size(x_16);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite_x3f___spec__1(x_16, x_20, x_19);
x_22 = lean_box(0);
x_23 = lean_array_get_size(x_21);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
x_27 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(x_1, x_3, x_4, x_6, x_26, x_21, x_24, x_25, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
lean_ctor_set(x_27, 0, x_22);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2;
x_45 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_49 = lean_unbox(x_46);
lean_dec(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_apply_8(x_48, x_50, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_52 = l_Lean_stringToMessageData(x_5);
x_53 = l_Lean_Meta_Simp_rewrite_x3f___closed__3;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Meta_Simp_rewrite_x3f___closed__5;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_MessageData_ofExpr(x_1);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6(x_44, x_60, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_apply_8(x_48, x_62, x_7, x_8, x_9, x_10, x_11, x_12, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_15);
if (x_65 == 0)
{
return x_15;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_15, 0);
x_67 = lean_ctor_get(x_15, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_15);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(x_1, x_2, x_3, x_17, x_5, x_6, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_rewrite_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_apply_8(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l_Lean_Meta_Simp_Step_result(x_19);
x_21 = l_Lean_Meta_Simp_mkEqTrans(x_10, x_20, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_Meta_Simp_Step_updateResult(x_19, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = l_Lean_Meta_Simp_Step_updateResult(x_19, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_19);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_9);
return x_37;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkNoConfusion(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4;
x_12 = lean_array_push(x_11, x_1);
x_13 = 0;
x_14 = 1;
x_15 = 1;
x_16 = l_Lean_Meta_mkLambdaFVars(x_12, x_9, x_13, x_14, x_15, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkEqFalse_x27(x_17, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2;
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_14 = l_Lean_Expr_appArg_x21(x_1);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 3;
lean_ctor_set_uint8(x_16, 5, x_18);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_whnf(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = lean_whnf(x_14, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_5, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 0;
lean_inc(x_29);
x_31 = l_Lean_Expr_constructorApp_x3f(x_29, x_20, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_constructorApp_x3f(x_29, x_23, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_33);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_name_eq(x_40, x_42);
lean_dec(x_42);
lean_dec(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
lean_free_object(x_25);
x_44 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4;
x_45 = 0;
x_46 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5;
x_47 = 0;
x_48 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_44, x_45, x_1, x_46, x_47, x_2, x_3, x_4, x_5, x_28);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_48);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_25, 0, x_57);
return x_25;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_25, 0);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_25);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = 0;
lean_inc(x_60);
x_62 = l_Lean_Expr_constructorApp_x3f(x_60, x_20, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_Expr_constructorApp_x3f(x_60, x_23, x_61);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_name_eq(x_73, x_75);
lean_dec(x_75);
lean_dec(x_73);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_77 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4;
x_78 = 0;
x_79 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5;
x_80 = 0;
x_81 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_77, x_78, x_1, x_79, x_80, x_2, x_3, x_4, x_5, x_59);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_59);
return x_91;
}
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_22);
if (x_92 == 0)
{
return x_22;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_22, 0);
x_94 = lean_ctor_get(x_22, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_22);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_2);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_19);
if (x_96 == 0)
{
return x_19;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_19, 0);
x_98 = lean_ctor_get(x_19, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_19);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
x_100 = lean_ctor_get_uint8(x_16, 0);
x_101 = lean_ctor_get_uint8(x_16, 1);
x_102 = lean_ctor_get_uint8(x_16, 2);
x_103 = lean_ctor_get_uint8(x_16, 3);
x_104 = lean_ctor_get_uint8(x_16, 4);
x_105 = lean_ctor_get_uint8(x_16, 6);
x_106 = lean_ctor_get_uint8(x_16, 7);
x_107 = lean_ctor_get_uint8(x_16, 8);
x_108 = lean_ctor_get_uint8(x_16, 9);
x_109 = lean_ctor_get_uint8(x_16, 10);
x_110 = lean_ctor_get_uint8(x_16, 11);
x_111 = lean_ctor_get_uint8(x_16, 12);
lean_dec(x_16);
x_112 = 3;
x_113 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_113, 0, x_100);
lean_ctor_set_uint8(x_113, 1, x_101);
lean_ctor_set_uint8(x_113, 2, x_102);
lean_ctor_set_uint8(x_113, 3, x_103);
lean_ctor_set_uint8(x_113, 4, x_104);
lean_ctor_set_uint8(x_113, 5, x_112);
lean_ctor_set_uint8(x_113, 6, x_105);
lean_ctor_set_uint8(x_113, 7, x_106);
lean_ctor_set_uint8(x_113, 8, x_107);
lean_ctor_set_uint8(x_113, 9, x_108);
lean_ctor_set_uint8(x_113, 10, x_109);
lean_ctor_set_uint8(x_113, 11, x_110);
lean_ctor_set_uint8(x_113, 12, x_111);
lean_ctor_set(x_2, 0, x_113);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_114 = lean_whnf(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_117 = lean_whnf(x_14, x_2, x_3, x_4, x_5, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_st_ref_get(x_5, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
lean_dec(x_121);
x_125 = 0;
lean_inc(x_124);
x_126 = l_Lean_Expr_constructorApp_x3f(x_124, x_115, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_124);
lean_dec(x_118);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_127 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_123;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_122);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
lean_dec(x_126);
x_130 = l_Lean_Expr_constructorApp_x3f(x_124, x_118, x_125);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_129);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_131 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_123;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_122);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
lean_dec(x_129);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_name_eq(x_137, x_139);
lean_dec(x_139);
lean_dec(x_137);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; 
lean_dec(x_123);
x_141 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4;
x_142 = 0;
x_143 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5;
x_144 = 0;
x_145 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_141, x_142, x_1, x_143, x_144, x_2, x_3, x_4, x_5, x_122);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_145, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_145, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_152 = x_145;
} else {
 lean_dec_ref(x_145);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_154 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_123;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_122);
return x_155;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_115);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_156 = lean_ctor_get(x_117, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_117, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_158 = x_117;
} else {
 lean_dec_ref(x_117);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_2);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_160 = lean_ctor_get(x_114, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_114, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_162 = x_114;
} else {
 lean_dec_ref(x_114);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_164 = lean_ctor_get(x_2, 0);
x_165 = lean_ctor_get(x_2, 1);
x_166 = lean_ctor_get(x_2, 2);
x_167 = lean_ctor_get(x_2, 3);
x_168 = lean_ctor_get(x_2, 4);
x_169 = lean_ctor_get(x_2, 5);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_2);
x_170 = lean_ctor_get_uint8(x_164, 0);
x_171 = lean_ctor_get_uint8(x_164, 1);
x_172 = lean_ctor_get_uint8(x_164, 2);
x_173 = lean_ctor_get_uint8(x_164, 3);
x_174 = lean_ctor_get_uint8(x_164, 4);
x_175 = lean_ctor_get_uint8(x_164, 6);
x_176 = lean_ctor_get_uint8(x_164, 7);
x_177 = lean_ctor_get_uint8(x_164, 8);
x_178 = lean_ctor_get_uint8(x_164, 9);
x_179 = lean_ctor_get_uint8(x_164, 10);
x_180 = lean_ctor_get_uint8(x_164, 11);
x_181 = lean_ctor_get_uint8(x_164, 12);
if (lean_is_exclusive(x_164)) {
 x_182 = x_164;
} else {
 lean_dec_ref(x_164);
 x_182 = lean_box(0);
}
x_183 = 3;
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 0, 13);
} else {
 x_184 = x_182;
}
lean_ctor_set_uint8(x_184, 0, x_170);
lean_ctor_set_uint8(x_184, 1, x_171);
lean_ctor_set_uint8(x_184, 2, x_172);
lean_ctor_set_uint8(x_184, 3, x_173);
lean_ctor_set_uint8(x_184, 4, x_174);
lean_ctor_set_uint8(x_184, 5, x_183);
lean_ctor_set_uint8(x_184, 6, x_175);
lean_ctor_set_uint8(x_184, 7, x_176);
lean_ctor_set_uint8(x_184, 8, x_177);
lean_ctor_set_uint8(x_184, 9, x_178);
lean_ctor_set_uint8(x_184, 10, x_179);
lean_ctor_set_uint8(x_184, 11, x_180);
lean_ctor_set_uint8(x_184, 12, x_181);
x_185 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_165);
lean_ctor_set(x_185, 2, x_166);
lean_ctor_set(x_185, 3, x_167);
lean_ctor_set(x_185, 4, x_168);
lean_ctor_set(x_185, 5, x_169);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_185);
x_186 = lean_whnf(x_13, x_185, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_185);
x_189 = lean_whnf(x_14, x_185, x_3, x_4, x_5, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_st_ref_get(x_5, x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_195 = x_192;
} else {
 lean_dec_ref(x_192);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
lean_dec(x_193);
x_197 = 0;
lean_inc(x_196);
x_198 = l_Lean_Expr_constructorApp_x3f(x_196, x_187, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_196);
lean_dec(x_190);
lean_dec(x_185);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_199 = lean_box(0);
if (lean_is_scalar(x_195)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_195;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_194);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
lean_dec(x_198);
x_202 = l_Lean_Expr_constructorApp_x3f(x_196, x_190, x_197);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_201);
lean_dec(x_185);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_203 = lean_box(0);
if (lean_is_scalar(x_195)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_195;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_194);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_205 = lean_ctor_get(x_202, 0);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_ctor_get(x_201, 0);
lean_inc(x_206);
lean_dec(x_201);
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_ctor_get(x_207, 0);
lean_inc(x_210);
lean_dec(x_207);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_name_eq(x_209, x_211);
lean_dec(x_211);
lean_dec(x_209);
if (x_212 == 0)
{
lean_object* x_213; uint8_t x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
lean_dec(x_195);
x_213 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4;
x_214 = 0;
x_215 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5;
x_216 = 0;
x_217 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_213, x_214, x_1, x_215, x_216, x_185, x_3, x_4, x_5, x_194);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_217, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_217, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_224 = x_217;
} else {
 lean_dec_ref(x_217);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_185);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_226 = lean_box(0);
if (lean_is_scalar(x_195)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_195;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_194);
return x_227;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_228 = lean_ctor_get(x_189, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_189, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_230 = x_189;
} else {
 lean_dec_ref(x_189);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_185);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_232 = lean_ctor_get(x_186, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_186, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_234 = x_186;
} else {
 lean_dec_ref(x_186);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteCtorEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_rewriteCtorEq_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_10, 0, x_21);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_9, 0, x_24);
return x_9;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_27 = x_10;
} else {
 lean_dec_ref(x_10);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteCtorEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_tryRewriteCtorEq_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("True", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_false_of_decide", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_true_of_decide", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasFVar(x_1);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasMVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2;
x_10 = l_Lean_Expr_isConstOf(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2;
x_12 = l_Lean_Expr_isConstOf(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_2, 3);
x_19 = lean_ctor_get(x_2, 4);
x_20 = lean_ctor_get(x_2, 5);
x_21 = lean_ctor_get_uint8(x_14, 0);
x_22 = lean_ctor_get_uint8(x_14, 1);
x_23 = lean_ctor_get_uint8(x_14, 2);
x_24 = lean_ctor_get_uint8(x_14, 3);
x_25 = lean_ctor_get_uint8(x_14, 4);
x_26 = lean_ctor_get_uint8(x_14, 6);
x_27 = lean_ctor_get_uint8(x_14, 7);
x_28 = lean_ctor_get_uint8(x_14, 8);
x_29 = lean_ctor_get_uint8(x_14, 9);
x_30 = lean_ctor_get_uint8(x_14, 10);
x_31 = lean_ctor_get_uint8(x_14, 11);
x_32 = lean_ctor_get_uint8(x_14, 12);
x_33 = 3;
lean_ctor_set_uint8(x_14, 5, x_33);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_34 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_38, 0, x_21);
lean_ctor_set_uint8(x_38, 1, x_22);
lean_ctor_set_uint8(x_38, 2, x_23);
lean_ctor_set_uint8(x_38, 3, x_24);
lean_ctor_set_uint8(x_38, 4, x_25);
lean_ctor_set_uint8(x_38, 5, x_37);
lean_ctor_set_uint8(x_38, 6, x_26);
lean_ctor_set_uint8(x_38, 7, x_27);
lean_ctor_set_uint8(x_38, 8, x_28);
lean_ctor_set_uint8(x_38, 9, x_29);
lean_ctor_set_uint8(x_38, 10, x_30);
lean_ctor_set_uint8(x_38, 11, x_31);
lean_ctor_set_uint8(x_38, 12, x_32);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_16);
lean_ctor_set(x_39, 2, x_17);
lean_ctor_set(x_39, 3, x_18);
lean_ctor_set(x_39, 4, x_19);
lean_ctor_set(x_39, 5, x_20);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_35);
x_40 = lean_whnf(x_35, x_39, x_3, x_4, x_5, x_36);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
x_45 = l_Lean_Expr_isConstOf(x_42, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
x_47 = l_Lean_Expr_isConstOf(x_42, x_46);
lean_dec(x_42);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_box(0);
lean_ctor_set(x_40, 0, x_48);
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_free_object(x_40);
x_49 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8;
x_50 = l_Lean_Meta_mkEqRefl(x_49, x_2, x_3, x_4, x_5, x_43);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l_Lean_Expr_appArg_x21(x_35);
lean_dec(x_35);
x_54 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_55 = lean_array_push(x_54, x_1);
x_56 = lean_array_push(x_55, x_53);
x_57 = lean_array_push(x_56, x_52);
x_58 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
x_59 = l_Lean_mkAppN(x_58, x_57);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_50, 0, x_64);
return x_50;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_65 = lean_ctor_get(x_50, 0);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_50);
x_67 = l_Lean_Expr_appArg_x21(x_35);
lean_dec(x_35);
x_68 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_69 = lean_array_push(x_68, x_1);
x_70 = lean_array_push(x_69, x_67);
x_71 = lean_array_push(x_70, x_65);
x_72 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
x_73 = l_Lean_mkAppN(x_72, x_71);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_66);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_35);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_50);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_50, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_ctor_set_tag(x_50, 0);
lean_ctor_set(x_50, 0, x_82);
return x_50;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_50, 1);
lean_inc(x_83);
lean_dec(x_50);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_free_object(x_40);
lean_dec(x_42);
x_86 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13;
x_87 = l_Lean_Meta_mkEqRefl(x_86, x_2, x_3, x_4, x_5, x_43);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = l_Lean_Expr_appArg_x21(x_35);
lean_dec(x_35);
x_91 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_92 = lean_array_push(x_91, x_1);
x_93 = lean_array_push(x_92, x_90);
x_94 = lean_array_push(x_93, x_89);
x_95 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
x_96 = l_Lean_mkAppN(x_95, x_94);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
x_99 = lean_unsigned_to_nat(0u);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_97);
lean_ctor_set(x_100, 2, x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_87, 0, x_101);
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_102 = lean_ctor_get(x_87, 0);
x_103 = lean_ctor_get(x_87, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_87);
x_104 = l_Lean_Expr_appArg_x21(x_35);
lean_dec(x_35);
x_105 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_106 = lean_array_push(x_105, x_1);
x_107 = lean_array_push(x_106, x_104);
x_108 = lean_array_push(x_107, x_102);
x_109 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
x_110 = l_Lean_mkAppN(x_109, x_108);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
x_113 = lean_unsigned_to_nat(0u);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_111);
lean_ctor_set(x_114, 2, x_113);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_103);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_35);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_87);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_87, 0);
lean_dec(x_118);
x_119 = lean_box(0);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_119);
return x_87;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_87, 1);
lean_inc(x_120);
lean_dec(x_87);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_ctor_get(x_40, 0);
x_124 = lean_ctor_get(x_40, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_40);
x_125 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
x_126 = l_Lean_Expr_isConstOf(x_123, x_125);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
x_128 = l_Lean_Expr_isConstOf(x_123, x_127);
lean_dec(x_123);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_124);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8;
x_132 = l_Lean_Meta_mkEqRefl(x_131, x_2, x_3, x_4, x_5, x_124);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = l_Lean_Expr_appArg_x21(x_35);
lean_dec(x_35);
x_137 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_138 = lean_array_push(x_137, x_1);
x_139 = lean_array_push(x_138, x_136);
x_140 = lean_array_push(x_139, x_133);
x_141 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
x_142 = l_Lean_mkAppN(x_141, x_140);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_143);
lean_ctor_set(x_146, 2, x_145);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
if (lean_is_scalar(x_135)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_135;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_134);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_35);
lean_dec(x_1);
x_149 = lean_ctor_get(x_132, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_150 = x_132;
} else {
 lean_dec_ref(x_132);
 x_150 = lean_box(0);
}
x_151 = lean_box(0);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
 lean_ctor_set_tag(x_152, 0);
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_123);
x_153 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13;
x_154 = l_Lean_Meta_mkEqRefl(x_153, x_2, x_3, x_4, x_5, x_124);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = l_Lean_Expr_appArg_x21(x_35);
lean_dec(x_35);
x_159 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_160 = lean_array_push(x_159, x_1);
x_161 = lean_array_push(x_160, x_158);
x_162 = lean_array_push(x_161, x_155);
x_163 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
x_164 = l_Lean_mkAppN(x_163, x_162);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_165);
lean_ctor_set(x_168, 2, x_167);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
if (lean_is_scalar(x_157)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_157;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_156);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_35);
lean_dec(x_1);
x_171 = lean_ctor_get(x_154, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_172 = x_154;
} else {
 lean_dec_ref(x_154);
 x_172 = lean_box(0);
}
x_173 = lean_box(0);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
 lean_ctor_set_tag(x_174, 0);
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_40);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_40, 0);
lean_dec(x_176);
x_177 = lean_box(0);
lean_ctor_set_tag(x_40, 0);
lean_ctor_set(x_40, 0, x_177);
return x_40;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_40, 1);
lean_inc(x_178);
lean_dec(x_40);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_2);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_34);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_34, 0);
lean_dec(x_182);
x_183 = lean_box(0);
lean_ctor_set_tag(x_34, 0);
lean_ctor_set(x_34, 0, x_183);
return x_34;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_34, 1);
lean_inc(x_184);
lean_dec(x_34);
x_185 = lean_box(0);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; 
x_187 = lean_ctor_get(x_2, 1);
x_188 = lean_ctor_get(x_2, 2);
x_189 = lean_ctor_get(x_2, 3);
x_190 = lean_ctor_get(x_2, 4);
x_191 = lean_ctor_get(x_2, 5);
x_192 = lean_ctor_get_uint8(x_14, 0);
x_193 = lean_ctor_get_uint8(x_14, 1);
x_194 = lean_ctor_get_uint8(x_14, 2);
x_195 = lean_ctor_get_uint8(x_14, 3);
x_196 = lean_ctor_get_uint8(x_14, 4);
x_197 = lean_ctor_get_uint8(x_14, 6);
x_198 = lean_ctor_get_uint8(x_14, 7);
x_199 = lean_ctor_get_uint8(x_14, 8);
x_200 = lean_ctor_get_uint8(x_14, 9);
x_201 = lean_ctor_get_uint8(x_14, 10);
x_202 = lean_ctor_get_uint8(x_14, 11);
x_203 = lean_ctor_get_uint8(x_14, 12);
lean_dec(x_14);
x_204 = 3;
x_205 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_205, 0, x_192);
lean_ctor_set_uint8(x_205, 1, x_193);
lean_ctor_set_uint8(x_205, 2, x_194);
lean_ctor_set_uint8(x_205, 3, x_195);
lean_ctor_set_uint8(x_205, 4, x_196);
lean_ctor_set_uint8(x_205, 5, x_204);
lean_ctor_set_uint8(x_205, 6, x_197);
lean_ctor_set_uint8(x_205, 7, x_198);
lean_ctor_set_uint8(x_205, 8, x_199);
lean_ctor_set_uint8(x_205, 9, x_200);
lean_ctor_set_uint8(x_205, 10, x_201);
lean_ctor_set_uint8(x_205, 11, x_202);
lean_ctor_set_uint8(x_205, 12, x_203);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_ctor_set(x_2, 0, x_205);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_206 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = 1;
x_210 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_210, 0, x_192);
lean_ctor_set_uint8(x_210, 1, x_193);
lean_ctor_set_uint8(x_210, 2, x_194);
lean_ctor_set_uint8(x_210, 3, x_195);
lean_ctor_set_uint8(x_210, 4, x_196);
lean_ctor_set_uint8(x_210, 5, x_209);
lean_ctor_set_uint8(x_210, 6, x_197);
lean_ctor_set_uint8(x_210, 7, x_198);
lean_ctor_set_uint8(x_210, 8, x_199);
lean_ctor_set_uint8(x_210, 9, x_200);
lean_ctor_set_uint8(x_210, 10, x_201);
lean_ctor_set_uint8(x_210, 11, x_202);
lean_ctor_set_uint8(x_210, 12, x_203);
x_211 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_187);
lean_ctor_set(x_211, 2, x_188);
lean_ctor_set(x_211, 3, x_189);
lean_ctor_set(x_211, 4, x_190);
lean_ctor_set(x_211, 5, x_191);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_207);
x_212 = lean_whnf(x_207, x_211, x_3, x_4, x_5, x_208);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
x_216 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
x_217 = l_Lean_Expr_isConstOf(x_213, x_216);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
x_219 = l_Lean_Expr_isConstOf(x_213, x_218);
lean_dec(x_213);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_207);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_220 = lean_box(0);
if (lean_is_scalar(x_215)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_215;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_214);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_215);
x_222 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8;
x_223 = l_Lean_Meta_mkEqRefl(x_222, x_2, x_3, x_4, x_5, x_214);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_227 = l_Lean_Expr_appArg_x21(x_207);
lean_dec(x_207);
x_228 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_229 = lean_array_push(x_228, x_1);
x_230 = lean_array_push(x_229, x_227);
x_231 = lean_array_push(x_230, x_224);
x_232 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
x_233 = l_Lean_mkAppN(x_232, x_231);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_233);
x_235 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
x_236 = lean_unsigned_to_nat(0u);
x_237 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_234);
lean_ctor_set(x_237, 2, x_236);
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_237);
if (lean_is_scalar(x_226)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_226;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_225);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_207);
lean_dec(x_1);
x_240 = lean_ctor_get(x_223, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_241 = x_223;
} else {
 lean_dec_ref(x_223);
 x_241 = lean_box(0);
}
x_242 = lean_box(0);
if (lean_is_scalar(x_241)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_241;
 lean_ctor_set_tag(x_243, 0);
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_240);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_215);
lean_dec(x_213);
x_244 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13;
x_245 = l_Lean_Meta_mkEqRefl(x_244, x_2, x_3, x_4, x_5, x_214);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_248 = x_245;
} else {
 lean_dec_ref(x_245);
 x_248 = lean_box(0);
}
x_249 = l_Lean_Expr_appArg_x21(x_207);
lean_dec(x_207);
x_250 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_251 = lean_array_push(x_250, x_1);
x_252 = lean_array_push(x_251, x_249);
x_253 = lean_array_push(x_252, x_246);
x_254 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
x_255 = l_Lean_mkAppN(x_254, x_253);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
x_257 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
x_258 = lean_unsigned_to_nat(0u);
x_259 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_256);
lean_ctor_set(x_259, 2, x_258);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
if (lean_is_scalar(x_248)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_248;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_247);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_207);
lean_dec(x_1);
x_262 = lean_ctor_get(x_245, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_263 = x_245;
} else {
 lean_dec_ref(x_245);
 x_263 = lean_box(0);
}
x_264 = lean_box(0);
if (lean_is_scalar(x_263)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_263;
 lean_ctor_set_tag(x_265, 0);
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_262);
return x_265;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_207);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_266 = lean_ctor_get(x_212, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_267 = x_212;
} else {
 lean_dec_ref(x_212);
 x_267 = lean_box(0);
}
x_268 = lean_box(0);
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_267;
 lean_ctor_set_tag(x_269, 0);
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_266);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_2);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_270 = lean_ctor_get(x_206, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_271 = x_206;
} else {
 lean_dec_ref(x_206);
 x_271 = lean_box(0);
}
x_272 = lean_box(0);
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_271;
 lean_ctor_set_tag(x_273, 0);
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_270);
return x_273;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; uint8_t x_283; uint8_t x_284; uint8_t x_285; uint8_t x_286; uint8_t x_287; uint8_t x_288; uint8_t x_289; uint8_t x_290; uint8_t x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_274 = lean_ctor_get(x_2, 0);
x_275 = lean_ctor_get(x_2, 1);
x_276 = lean_ctor_get(x_2, 2);
x_277 = lean_ctor_get(x_2, 3);
x_278 = lean_ctor_get(x_2, 4);
x_279 = lean_ctor_get(x_2, 5);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_2);
x_280 = lean_ctor_get_uint8(x_274, 0);
x_281 = lean_ctor_get_uint8(x_274, 1);
x_282 = lean_ctor_get_uint8(x_274, 2);
x_283 = lean_ctor_get_uint8(x_274, 3);
x_284 = lean_ctor_get_uint8(x_274, 4);
x_285 = lean_ctor_get_uint8(x_274, 6);
x_286 = lean_ctor_get_uint8(x_274, 7);
x_287 = lean_ctor_get_uint8(x_274, 8);
x_288 = lean_ctor_get_uint8(x_274, 9);
x_289 = lean_ctor_get_uint8(x_274, 10);
x_290 = lean_ctor_get_uint8(x_274, 11);
x_291 = lean_ctor_get_uint8(x_274, 12);
if (lean_is_exclusive(x_274)) {
 x_292 = x_274;
} else {
 lean_dec_ref(x_274);
 x_292 = lean_box(0);
}
x_293 = 3;
if (lean_is_scalar(x_292)) {
 x_294 = lean_alloc_ctor(0, 0, 13);
} else {
 x_294 = x_292;
}
lean_ctor_set_uint8(x_294, 0, x_280);
lean_ctor_set_uint8(x_294, 1, x_281);
lean_ctor_set_uint8(x_294, 2, x_282);
lean_ctor_set_uint8(x_294, 3, x_283);
lean_ctor_set_uint8(x_294, 4, x_284);
lean_ctor_set_uint8(x_294, 5, x_293);
lean_ctor_set_uint8(x_294, 6, x_285);
lean_ctor_set_uint8(x_294, 7, x_286);
lean_ctor_set_uint8(x_294, 8, x_287);
lean_ctor_set_uint8(x_294, 9, x_288);
lean_ctor_set_uint8(x_294, 10, x_289);
lean_ctor_set_uint8(x_294, 11, x_290);
lean_ctor_set_uint8(x_294, 12, x_291);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
x_295 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_275);
lean_ctor_set(x_295, 2, x_276);
lean_ctor_set(x_295, 3, x_277);
lean_ctor_set(x_295, 4, x_278);
lean_ctor_set(x_295, 5, x_279);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_295);
lean_inc(x_1);
x_296 = l_Lean_Meta_mkDecide(x_1, x_295, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = 1;
x_300 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_300, 0, x_280);
lean_ctor_set_uint8(x_300, 1, x_281);
lean_ctor_set_uint8(x_300, 2, x_282);
lean_ctor_set_uint8(x_300, 3, x_283);
lean_ctor_set_uint8(x_300, 4, x_284);
lean_ctor_set_uint8(x_300, 5, x_299);
lean_ctor_set_uint8(x_300, 6, x_285);
lean_ctor_set_uint8(x_300, 7, x_286);
lean_ctor_set_uint8(x_300, 8, x_287);
lean_ctor_set_uint8(x_300, 9, x_288);
lean_ctor_set_uint8(x_300, 10, x_289);
lean_ctor_set_uint8(x_300, 11, x_290);
lean_ctor_set_uint8(x_300, 12, x_291);
x_301 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_275);
lean_ctor_set(x_301, 2, x_276);
lean_ctor_set(x_301, 3, x_277);
lean_ctor_set(x_301, 4, x_278);
lean_ctor_set(x_301, 5, x_279);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_297);
x_302 = lean_whnf(x_297, x_301, x_3, x_4, x_5, x_298);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_305 = x_302;
} else {
 lean_dec_ref(x_302);
 x_305 = lean_box(0);
}
x_306 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
x_307 = l_Lean_Expr_isConstOf(x_303, x_306);
if (x_307 == 0)
{
lean_object* x_308; uint8_t x_309; 
x_308 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
x_309 = l_Lean_Expr_isConstOf(x_303, x_308);
lean_dec(x_303);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
lean_dec(x_297);
lean_dec(x_295);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_310 = lean_box(0);
if (lean_is_scalar(x_305)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_305;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_304);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_305);
x_312 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8;
x_313 = l_Lean_Meta_mkEqRefl(x_312, x_295, x_3, x_4, x_5, x_304);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_316 = x_313;
} else {
 lean_dec_ref(x_313);
 x_316 = lean_box(0);
}
x_317 = l_Lean_Expr_appArg_x21(x_297);
lean_dec(x_297);
x_318 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_319 = lean_array_push(x_318, x_1);
x_320 = lean_array_push(x_319, x_317);
x_321 = lean_array_push(x_320, x_314);
x_322 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
x_323 = l_Lean_mkAppN(x_322, x_321);
x_324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_324, 0, x_323);
x_325 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
x_326 = lean_unsigned_to_nat(0u);
x_327 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_324);
lean_ctor_set(x_327, 2, x_326);
x_328 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_328, 0, x_327);
if (lean_is_scalar(x_316)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_316;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_315);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_297);
lean_dec(x_1);
x_330 = lean_ctor_get(x_313, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_331 = x_313;
} else {
 lean_dec_ref(x_313);
 x_331 = lean_box(0);
}
x_332 = lean_box(0);
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_331;
 lean_ctor_set_tag(x_333, 0);
}
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_330);
return x_333;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_305);
lean_dec(x_303);
x_334 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13;
x_335 = l_Lean_Meta_mkEqRefl(x_334, x_295, x_3, x_4, x_5, x_304);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_338 = x_335;
} else {
 lean_dec_ref(x_335);
 x_338 = lean_box(0);
}
x_339 = l_Lean_Expr_appArg_x21(x_297);
lean_dec(x_297);
x_340 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_341 = lean_array_push(x_340, x_1);
x_342 = lean_array_push(x_341, x_339);
x_343 = lean_array_push(x_342, x_336);
x_344 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
x_345 = l_Lean_mkAppN(x_344, x_343);
x_346 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_346, 0, x_345);
x_347 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
x_348 = lean_unsigned_to_nat(0u);
x_349 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_346);
lean_ctor_set(x_349, 2, x_348);
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_349);
if (lean_is_scalar(x_338)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_338;
}
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_337);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_297);
lean_dec(x_1);
x_352 = lean_ctor_get(x_335, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_353 = x_335;
} else {
 lean_dec_ref(x_335);
 x_353 = lean_box(0);
}
x_354 = lean_box(0);
if (lean_is_scalar(x_353)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_353;
 lean_ctor_set_tag(x_355, 0);
}
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_352);
return x_355;
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_297);
lean_dec(x_295);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_356 = lean_ctor_get(x_302, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_357 = x_302;
} else {
 lean_dec_ref(x_302);
 x_357 = lean_box(0);
}
x_358 = lean_box(0);
if (lean_is_scalar(x_357)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_357;
 lean_ctor_set_tag(x_359, 0);
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_356);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_295);
lean_dec(x_279);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_360 = lean_ctor_get(x_296, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_361 = x_296;
} else {
 lean_dec_ref(x_296);
 x_361 = lean_box(0);
}
x_362 = lean_box(0);
if (lean_is_scalar(x_361)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_361;
 lean_ctor_set_tag(x_363, 0);
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_360);
return x_363;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_364 = lean_box(0);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_6);
return x_365;
}
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_366 = lean_box(0);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_6);
return x_367;
}
}
else
{
lean_object* x_368; lean_object* x_369; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_368 = lean_box(0);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_6);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_370 = lean_box(0);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_6);
return x_371;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteUsingDecide_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*2 + 9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_14, 0, x_25);
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_13, 0, x_28);
return x_13;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_31 = x_14;
} else {
 lean_dec_ref(x_14);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteUsingDecide_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_tryRewriteUsingDecide_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_Meta_Linear_simp_x3f(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_12);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_11, 0, x_28);
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_12, 0, x_32);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_12);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_12, 0);
lean_inc(x_38);
lean_dec(x_12);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_40 = x_11;
} else {
 lean_dec_ref(x_11);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
if (lean_is_scalar(x_40)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_40;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_11);
if (x_49 == 0)
{
return x_11;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_11, 0);
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_11);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*2 + 10);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Simp_simpArith_x3f___lambda__1(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_simpArith_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_17 = lean_array_uget(x_4, x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_17);
x_18 = l_Lean_Meta_isRflTheorem(x_17, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
lean_inc(x_17);
x_22 = l_Lean_Expr_const___override(x_17, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_17);
x_24 = l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___closed__1;
x_25 = lean_unsigned_to_nat(1000u);
x_26 = 1;
x_27 = 0;
x_28 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*5 + 1, x_27);
x_29 = lean_unbox(x_19);
lean_dec(x_19);
lean_ctor_set_uint8(x_28, sizeof(void*)*5 + 2, x_29);
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_10, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 5);
lean_inc(x_35);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 2;
lean_ctor_set_uint8(x_30, 5, x_37);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_38, 2, x_32);
lean_ctor_set(x_38, 3, x_33);
lean_ctor_set(x_38, 4, x_34);
lean_ctor_set(x_38, 5, x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l_Lean_Meta_Simp_tryTheorem_x3f(x_1, x_28, x_2, x_8, x_9, x_38, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; size_t x_42; size_t x_43; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 1;
x_43 = lean_usize_add(x_6, x_42);
lean_inc(x_3);
{
size_t _tmp_5 = x_43;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_13 = x_41;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_14 = _tmp_13;
}
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_39, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_40, 0, x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_40);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_39, 0, x_52);
return x_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_39, 0, x_58);
return x_39;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_39, 1);
lean_inc(x_59);
lean_dec(x_39);
x_60 = lean_ctor_get(x_40, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_61 = x_40;
} else {
 lean_dec_ref(x_40);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_60);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_59);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_39);
if (x_68 == 0)
{
return x_39;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_39, 0);
x_70 = lean_ctor_get(x_39, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_39);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get_uint8(x_30, 0);
x_73 = lean_ctor_get_uint8(x_30, 1);
x_74 = lean_ctor_get_uint8(x_30, 2);
x_75 = lean_ctor_get_uint8(x_30, 3);
x_76 = lean_ctor_get_uint8(x_30, 4);
x_77 = lean_ctor_get_uint8(x_30, 6);
x_78 = lean_ctor_get_uint8(x_30, 7);
x_79 = lean_ctor_get_uint8(x_30, 8);
x_80 = lean_ctor_get_uint8(x_30, 9);
x_81 = lean_ctor_get_uint8(x_30, 10);
x_82 = lean_ctor_get_uint8(x_30, 11);
x_83 = lean_ctor_get_uint8(x_30, 12);
lean_dec(x_30);
x_84 = 2;
x_85 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_85, 0, x_72);
lean_ctor_set_uint8(x_85, 1, x_73);
lean_ctor_set_uint8(x_85, 2, x_74);
lean_ctor_set_uint8(x_85, 3, x_75);
lean_ctor_set_uint8(x_85, 4, x_76);
lean_ctor_set_uint8(x_85, 5, x_84);
lean_ctor_set_uint8(x_85, 6, x_77);
lean_ctor_set_uint8(x_85, 7, x_78);
lean_ctor_set_uint8(x_85, 8, x_79);
lean_ctor_set_uint8(x_85, 9, x_80);
lean_ctor_set_uint8(x_85, 10, x_81);
lean_ctor_set_uint8(x_85, 11, x_82);
lean_ctor_set_uint8(x_85, 12, x_83);
x_86 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_31);
lean_ctor_set(x_86, 2, x_32);
lean_ctor_set(x_86, 3, x_33);
lean_ctor_set(x_86, 4, x_34);
lean_ctor_set(x_86, 5, x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l_Lean_Meta_Simp_tryTheorem_x3f(x_1, x_28, x_2, x_8, x_9, x_86, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; size_t x_90; size_t x_91; 
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = 1;
x_91 = lean_usize_add(x_6, x_90);
lean_inc(x_3);
{
size_t _tmp_5 = x_91;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_13 = x_89;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_14 = _tmp_13;
}
goto _start;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_96 = x_88;
} else {
 lean_dec_ref(x_88);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_95);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
if (lean_is_scalar(x_94)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_94;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_93);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_ctor_get(x_87, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_87, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_105 = x_87;
} else {
 lean_dec_ref(x_87);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_18);
if (x_107 == 0)
{
return x_18;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_18, 0);
x_109 = lean_ctor_get(x_18, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_18);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = lean_get_match_equations_for(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_array_get_size(x_15);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1(x_2, x_3, x_20, x_15, x_18, x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_16);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_12, x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_16, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_24);
x_26 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___closed__1;
lean_inc(x_25);
x_27 = lean_mk_array(x_25, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_25, x_28);
lean_dec(x_25);
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_27, x_29);
x_31 = lean_array_get_size(x_30);
x_32 = l_Lean_Meta_Match_MatcherInfo_arity(x_23);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_34 = l_List_redLength___rarg(x_11);
x_35 = lean_mk_empty_array_with_capacity(x_34);
lean_dec(x_34);
x_36 = l_List_toArrayAux___rarg(x_11, x_35);
x_37 = lean_ctor_get(x_23, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
x_39 = l_Array_extract___rarg(x_30, x_24, x_38);
x_40 = lean_nat_dec_lt(x_38, x_31);
x_41 = lean_nat_add(x_38, x_28);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
x_43 = lean_nat_add(x_41, x_42);
lean_dec(x_42);
lean_inc(x_43);
lean_inc(x_30);
x_44 = l_Array_toSubarray___rarg(x_30, x_41, x_43);
x_45 = l_Array_ofSubarray___rarg(x_44);
x_46 = lean_ctor_get(x_23, 2);
lean_inc(x_46);
x_47 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_23);
lean_dec(x_23);
x_48 = lean_nat_add(x_43, x_47);
lean_dec(x_47);
lean_inc(x_48);
lean_inc(x_30);
x_49 = l_Array_toSubarray___rarg(x_30, x_43, x_48);
x_50 = l_Array_ofSubarray___rarg(x_49);
lean_inc(x_30);
x_51 = l_Array_toSubarray___rarg(x_30, x_48, x_31);
x_52 = l_Array_ofSubarray___rarg(x_51);
if (x_40 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_38);
lean_dec(x_30);
x_53 = l_Lean_instInhabitedExpr;
x_54 = l___private_Init_Util_0__outOfBounds___rarg(x_53);
x_55 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_36);
lean_ctor_set(x_55, 2, x_37);
lean_ctor_set(x_55, 3, x_39);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_45);
lean_ctor_set(x_55, 6, x_46);
lean_ctor_set(x_55, 7, x_50);
lean_ctor_set(x_55, 8, x_52);
lean_ctor_set(x_13, 0, x_55);
return x_12;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_array_fget(x_30, x_38);
lean_dec(x_38);
lean_dec(x_30);
x_57 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_57, 0, x_10);
lean_ctor_set(x_57, 1, x_36);
lean_ctor_set(x_57, 2, x_37);
lean_ctor_set(x_57, 3, x_39);
lean_ctor_set(x_57, 4, x_56);
lean_ctor_set(x_57, 5, x_45);
lean_ctor_set(x_57, 6, x_46);
lean_ctor_set(x_57, 7, x_50);
lean_ctor_set(x_57, 8, x_52);
lean_ctor_set(x_13, 0, x_57);
return x_12;
}
}
else
{
lean_object* x_58; 
lean_dec(x_31);
lean_dec(x_30);
lean_free_object(x_13);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
x_58 = lean_box(0);
lean_ctor_set(x_12, 0, x_58);
return x_12;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_59 = lean_ctor_get(x_13, 0);
lean_inc(x_59);
lean_dec(x_13);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_60);
x_62 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___closed__1;
lean_inc(x_61);
x_63 = lean_mk_array(x_61, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_61, x_64);
lean_dec(x_61);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_63, x_65);
x_67 = lean_array_get_size(x_66);
x_68 = l_Lean_Meta_Match_MatcherInfo_arity(x_59);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_70 = l_List_redLength___rarg(x_11);
x_71 = lean_mk_empty_array_with_capacity(x_70);
lean_dec(x_70);
x_72 = l_List_toArrayAux___rarg(x_11, x_71);
x_73 = lean_ctor_get(x_59, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_59, 0);
lean_inc(x_74);
x_75 = l_Array_extract___rarg(x_66, x_60, x_74);
x_76 = lean_nat_dec_lt(x_74, x_67);
x_77 = lean_nat_add(x_74, x_64);
x_78 = lean_ctor_get(x_59, 1);
lean_inc(x_78);
x_79 = lean_nat_add(x_77, x_78);
lean_dec(x_78);
lean_inc(x_79);
lean_inc(x_66);
x_80 = l_Array_toSubarray___rarg(x_66, x_77, x_79);
x_81 = l_Array_ofSubarray___rarg(x_80);
x_82 = lean_ctor_get(x_59, 2);
lean_inc(x_82);
x_83 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_59);
lean_dec(x_59);
x_84 = lean_nat_add(x_79, x_83);
lean_dec(x_83);
lean_inc(x_84);
lean_inc(x_66);
x_85 = l_Array_toSubarray___rarg(x_66, x_79, x_84);
x_86 = l_Array_ofSubarray___rarg(x_85);
lean_inc(x_66);
x_87 = l_Array_toSubarray___rarg(x_66, x_84, x_67);
x_88 = l_Array_ofSubarray___rarg(x_87);
if (x_76 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_74);
lean_dec(x_66);
x_89 = l_Lean_instInhabitedExpr;
x_90 = l___private_Init_Util_0__outOfBounds___rarg(x_89);
x_91 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_91, 0, x_10);
lean_ctor_set(x_91, 1, x_72);
lean_ctor_set(x_91, 2, x_73);
lean_ctor_set(x_91, 3, x_75);
lean_ctor_set(x_91, 4, x_90);
lean_ctor_set(x_91, 5, x_81);
lean_ctor_set(x_91, 6, x_82);
lean_ctor_set(x_91, 7, x_86);
lean_ctor_set(x_91, 8, x_88);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_12, 0, x_92);
return x_12;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_array_fget(x_66, x_74);
lean_dec(x_74);
lean_dec(x_66);
x_94 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_94, 0, x_10);
lean_ctor_set(x_94, 1, x_72);
lean_ctor_set(x_94, 2, x_73);
lean_ctor_set(x_94, 3, x_75);
lean_ctor_set(x_94, 4, x_93);
lean_ctor_set(x_94, 5, x_81);
lean_ctor_set(x_94, 6, x_82);
lean_ctor_set(x_94, 7, x_86);
lean_ctor_set(x_94, 8, x_88);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_12, 0, x_95);
return x_12;
}
}
else
{
lean_object* x_96; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_59);
lean_dec(x_11);
lean_dec(x_10);
x_96 = lean_box(0);
lean_ctor_set(x_12, 0, x_96);
return x_12;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_97 = lean_ctor_get(x_12, 1);
lean_inc(x_97);
lean_dec(x_12);
x_98 = lean_ctor_get(x_13, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_99 = x_13;
} else {
 lean_dec_ref(x_13);
 x_99 = lean_box(0);
}
x_100 = lean_unsigned_to_nat(0u);
x_101 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_100);
x_102 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___closed__1;
lean_inc(x_101);
x_103 = lean_mk_array(x_101, x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_101, x_104);
lean_dec(x_101);
x_106 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_103, x_105);
x_107 = lean_array_get_size(x_106);
x_108 = l_Lean_Meta_Match_MatcherInfo_arity(x_98);
x_109 = lean_nat_dec_lt(x_107, x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_110 = l_List_redLength___rarg(x_11);
x_111 = lean_mk_empty_array_with_capacity(x_110);
lean_dec(x_110);
x_112 = l_List_toArrayAux___rarg(x_11, x_111);
x_113 = lean_ctor_get(x_98, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_98, 0);
lean_inc(x_114);
x_115 = l_Array_extract___rarg(x_106, x_100, x_114);
x_116 = lean_nat_dec_lt(x_114, x_107);
x_117 = lean_nat_add(x_114, x_104);
x_118 = lean_ctor_get(x_98, 1);
lean_inc(x_118);
x_119 = lean_nat_add(x_117, x_118);
lean_dec(x_118);
lean_inc(x_119);
lean_inc(x_106);
x_120 = l_Array_toSubarray___rarg(x_106, x_117, x_119);
x_121 = l_Array_ofSubarray___rarg(x_120);
x_122 = lean_ctor_get(x_98, 2);
lean_inc(x_122);
x_123 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_98);
lean_dec(x_98);
x_124 = lean_nat_add(x_119, x_123);
lean_dec(x_123);
lean_inc(x_124);
lean_inc(x_106);
x_125 = l_Array_toSubarray___rarg(x_106, x_119, x_124);
x_126 = l_Array_ofSubarray___rarg(x_125);
lean_inc(x_106);
x_127 = l_Array_toSubarray___rarg(x_106, x_124, x_107);
x_128 = l_Array_ofSubarray___rarg(x_127);
if (x_116 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_114);
lean_dec(x_106);
x_129 = l_Lean_instInhabitedExpr;
x_130 = l___private_Init_Util_0__outOfBounds___rarg(x_129);
x_131 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_131, 0, x_10);
lean_ctor_set(x_131, 1, x_112);
lean_ctor_set(x_131, 2, x_113);
lean_ctor_set(x_131, 3, x_115);
lean_ctor_set(x_131, 4, x_130);
lean_ctor_set(x_131, 5, x_121);
lean_ctor_set(x_131, 6, x_122);
lean_ctor_set(x_131, 7, x_126);
lean_ctor_set(x_131, 8, x_128);
if (lean_is_scalar(x_99)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_99;
}
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_97);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_array_fget(x_106, x_114);
lean_dec(x_114);
lean_dec(x_106);
x_135 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_135, 0, x_10);
lean_ctor_set(x_135, 1, x_112);
lean_ctor_set(x_135, 2, x_113);
lean_ctor_set(x_135, 3, x_115);
lean_ctor_set(x_135, 4, x_134);
lean_ctor_set(x_135, 5, x_121);
lean_ctor_set(x_135, 6, x_122);
lean_ctor_set(x_135, 7, x_126);
lean_ctor_set(x_135, 8, x_128);
if (lean_is_scalar(x_99)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_99;
}
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_97);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_10);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_97);
return x_139;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_9);
lean_dec(x_1);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_8);
return x_141;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*2 + 7);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_14 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_Meta_Simp_simpMatchCore_x3f(x_23, x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pre", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
x_18 = lean_array_uget(x_5, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 4);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_19, x_20, x_2, x_21, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_7, x_25);
lean_inc(x_4);
{
size_t _tmp_6 = x_26;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_14 = x_24;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_15 = _tmp_14;
}
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_23, 0, x_32);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_22, 0, x_34);
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_42 = x_23;
} else {
 lean_dec_ref(x_23);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_41);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_22);
if (x_48 == 0)
{
return x_22;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_array_get_size(x_11);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(x_1, x_2, x_3, x_16, x_11, x_14, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Simp_rewritePre___lambda__1(x_1, x_12, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_17, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(x_1, x_2, x_16, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_rewritePre___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_Simp_rewritePre(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("post", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
x_18 = lean_array_uget(x_5, x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 4);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_19, x_20, x_2, x_21, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_7, x_25);
lean_inc(x_4);
{
size_t _tmp_6 = x_26;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_14 = x_24;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_15 = _tmp_14;
}
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_23, 0, x_32);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_22, 0, x_34);
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_42 = x_23;
} else {
 lean_dec_ref(x_23);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_41);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_22);
if (x_48 == 0)
{
return x_22;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_array_get_size(x_11);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(x_1, x_2, x_3, x_16, x_11, x_14, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Simp_rewritePre___lambda__1(x_1, x_12, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_17, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(x_1, x_2, x_16, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_Simp_rewritePost(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_11 = l_Lean_Meta_Simp_rewritePre(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_34; uint8_t x_35; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
lean_dec(x_3);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*2 + 9);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_box(0);
x_16 = x_36;
x_17 = x_13;
goto block_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_38 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f(x_37, x_5, x_6, x_7, x_8, x_13);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(0);
x_16 = x_41;
x_17 = x_40;
goto block_33;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_39, 0, x_45);
x_16 = x_39;
x_17 = x_42;
goto block_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_16 = x_48;
x_17 = x_42;
goto block_33;
}
}
}
block_33:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_14)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_14;
}
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_12);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Meta_Simp_Step_result(x_19);
x_21 = l_Lean_Meta_Simp_mkEqTrans(x_15, x_20, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_Meta_Simp_Step_updateResult(x_19, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = l_Lean_Meta_Simp_Step_updateResult(x_19, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_19);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_11);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_11, 0);
lean_dec(x_50);
return x_11;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_dec(x_11);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_11);
if (x_53 == 0)
{
return x_11;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_Simp_rewritePost(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_12, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_119 = l_Lean_Meta_Simp_simpMatch_x3f(x_2, x_118, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
lean_dec(x_117);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_15 = x_12;
x_16 = x_121;
goto block_116;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_12);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
lean_dec(x_120);
x_124 = l_Lean_Meta_Simp_Step_result(x_123);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_125 = l_Lean_Meta_Simp_mkEqTrans(x_117, x_124, x_5, x_6, x_7, x_8, x_122);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_Meta_Simp_Step_updateResult(x_123, x_126);
x_15 = x_128;
x_16 = x_127;
goto block_116;
}
else
{
uint8_t x_129; 
lean_dec(x_123);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
return x_125;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_125);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_117);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = !lean_is_exclusive(x_119);
if (x_133 == 0)
{
return x_119;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_119, 0);
x_135 = lean_ctor_get(x_119, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_119);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_dec(x_2);
x_15 = x_12;
x_16 = x_13;
goto block_116;
}
block_116:
{
lean_object* x_17; lean_object* x_18; 
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_15, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_98 = l_Lean_Meta_Simp_simpArith_x3f(x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
lean_dec(x_96);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_17 = x_15;
x_18 = x_100;
goto block_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_15);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
lean_dec(x_99);
x_103 = l_Lean_Meta_Simp_Step_result(x_102);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_104 = l_Lean_Meta_Simp_mkEqTrans(x_96, x_103, x_5, x_6, x_7, x_8, x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Meta_Simp_Step_updateResult(x_102, x_105);
x_17 = x_107;
x_18 = x_106;
goto block_95;
}
else
{
uint8_t x_108; 
lean_dec(x_102);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_104);
if (x_108 == 0)
{
return x_104;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_104, 0);
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_104);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_96);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_98);
if (x_112 == 0)
{
return x_98;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_98, 0);
x_114 = lean_ctor_get(x_98, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_98);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_dec(x_4);
x_17 = x_15;
x_18 = x_16;
goto block_95;
}
block_95:
{
lean_object* x_19; lean_object* x_20; 
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_80; uint8_t x_81; 
x_66 = lean_ctor_get(x_17, 0);
lean_inc(x_66);
x_80 = lean_ctor_get(x_3, 0);
lean_inc(x_80);
lean_dec(x_3);
x_81 = lean_ctor_get_uint8(x_80, sizeof(void*)*2 + 9);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_box(0);
x_67 = x_82;
x_68 = x_18;
goto block_79;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_66, 0);
lean_inc(x_83);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_84 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f(x_83, x_5, x_6, x_7, x_8, x_18);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_box(0);
x_67 = x_87;
x_68 = x_86;
goto block_79;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_85, 0);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_85, 0, x_91);
x_67 = x_85;
x_68 = x_88;
goto block_79;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
lean_dec(x_85);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_67 = x_94;
x_68 = x_88;
goto block_79;
}
}
}
block_79:
{
if (lean_obj_tag(x_67) == 0)
{
lean_dec(x_66);
x_19 = x_17;
x_20 = x_68;
goto block_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_17);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Meta_Simp_Step_result(x_69);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_71 = l_Lean_Meta_Simp_mkEqTrans(x_66, x_70, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Meta_Simp_Step_updateResult(x_69, x_72);
x_19 = x_74;
x_20 = x_73;
goto block_65;
}
else
{
uint8_t x_75; 
lean_dec(x_69);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_71, 0);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_71);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
else
{
lean_dec(x_3);
x_19 = x_17;
x_20 = x_18;
goto block_65;
}
block_65:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Meta_Simp_rewriteCtorEq_x3f(x_22, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_19, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_32);
x_33 = l_Lean_Meta_Simp_Step_result(x_19);
x_34 = l_Lean_Meta_Simp_mkEqTrans(x_21, x_33, x_5, x_6, x_7, x_8, x_31);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lean_Meta_Simp_Step_updateResult(x_19, x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = l_Lean_Meta_Simp_Step_updateResult(x_19, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_19);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_19);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_dec(x_23);
x_47 = lean_ctor_get(x_24, 0);
lean_inc(x_47);
lean_dec(x_24);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Lean_Meta_Simp_Step_result(x_48);
x_50 = l_Lean_Meta_Simp_mkEqTrans(x_21, x_49, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = l_Lean_Meta_Simp_Step_updateResult(x_48, x_51);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_48);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_58 = x_50;
} else {
 lean_dec_ref(x_50);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_23);
if (x_60 == 0)
{
return x_23;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_23, 0);
x_62 = lean_ctor_get(x_23, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_23);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_14)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_14;
}
lean_ctor_set(x_64, 0, x_19);
lean_ctor_set(x_64, 1, x_20);
return x_64;
}
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_11);
if (x_137 == 0)
{
return x_11;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_11, 0);
x_139 = lean_ctor_get(x_11, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_11);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_ACLt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_LinearArith_Simp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ACLt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqsExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_LinearArith_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1);
l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__1 = _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__1);
l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__2 = _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__2);
l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__3 = _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__3);
l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__4 = _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___closed__4);
l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___closed__1 = _init_l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__6___closed__1);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__15 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__15);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__16 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__16);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___closed__4);
l_Lean_Meta_Simp_synthesizeArgs___closed__1 = _init_l_Lean_Meta_Simp_synthesizeArgs___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs___closed__1);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7);
l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1 = _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1);
l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2 = _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2);
l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3 = _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3);
l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1 = _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1);
l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2 = _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2);
l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3 = _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3);
l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4 = _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6);
l_Lean_Meta_Simp_rewrite_x3f___closed__1 = _init_l_Lean_Meta_Simp_rewrite_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_x3f___closed__1);
l_Lean_Meta_Simp_rewrite_x3f___closed__2 = _init_l_Lean_Meta_Simp_rewrite_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_x3f___closed__2);
l_Lean_Meta_Simp_rewrite_x3f___closed__3 = _init_l_Lean_Meta_Simp_rewrite_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_x3f___closed__3);
l_Lean_Meta_Simp_rewrite_x3f___closed__4 = _init_l_Lean_Meta_Simp_rewrite_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_x3f___closed__4);
l_Lean_Meta_Simp_rewrite_x3f___closed__5 = _init_l_Lean_Meta_Simp_rewrite_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_x3f___closed__5);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17);
l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___closed__1 = _init_l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
