// Lean compiler output
// Module: Lean.Server.FileWorker
// Imports: Init Init.System.IO Lean.Data.RBMap Lean.Environment Lean.Data.Lsp Lean.Data.Json.FromToJson Lean.Util.Paths Lean.LoadDynlib Lean.Server.Utils Lean.Server.Snapshots Lean.Server.AsyncList Lean.Server.References Lean.Server.FileWorker.Utils Lean.Server.FileWorker.RequestHandling Lean.Server.FileWorker.WidgetRequests Lean.Server.Rpc.Basic Lean.Widget.InteractiveDiagnostic
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1(size_t, size_t, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36;
static lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2;
uint8_t l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_workerMain___boxed__const__1;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__1;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Server_FileWorker_handleCancelRequest___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Server_FileWorker_queueRequest___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcReleaseParams____x40_Lean_Data_Lsp_Extra___hyg_2036_(lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1116____at_Lean_SearchPath_findAllWithExt___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2;
extern lean_object* l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58;
static lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_takeWhile___rarg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_Lean_Server_FileWorker_workerMain___closed__1;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__11;
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_has_finished(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23;
static lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__2;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__66;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_findModuleRefs(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at_Lean_Server_FileWorker_updateDocument___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
lean_object* l_IO_AsyncList_waitFind_x3f___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1;
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__1;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1;
static lean_object* l_Lean_Server_FileWorker_handleNotification___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1;
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__2;
static lean_object* l_Lean_Server_FileWorker_mainLoop___closed__2;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__3;
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__6(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_List_getLast_x21___rarg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_CancelToken_new(lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_mainLoop___closed__1;
lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_appDir(lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_diagnostics(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10;
lean_object* lean_get_stdin(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__5;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeExtension;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_FileWorker_updateDocument___spec__3(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__3;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__70;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__6;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_parseNextCmd(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleNotification___closed__2;
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_updateDocument___lambda__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__3(uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4;
lean_object* l_Lean_Server_maybeTee(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25;
lean_object* l_Lean_Server_Snapshots_compileNextCmd(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleDidChange___closed__5;
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151_(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_updateDocument___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
extern lean_object* l_Task_Priority_default;
lean_object* lean_get_prefix(lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1(lean_object*, uint64_t);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2;
lean_object* l_Lean_Server_publishProgressDone(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__4;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5;
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now(lean_object*);
lean_object* l_Lean_JsonNumber_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_module_name_of_file(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(lean_object*, uint64_t, lean_object*);
lean_object* l_Lean_Widget_msgToInteractiveDiagnostic(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleRequest___closed__1;
static uint8_t l_Lean_Server_FileWorker_handleDidChange___closed__3;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__64;
lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__72;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_unfoldCmdSnaps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_702_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdout(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal___closed__1;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at_Lean_Server_FileWorker_updateDocument___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleDocumentHighlight___spec__1(size_t, size_t, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_141_(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd_loop(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63;
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(uint64_t, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__73;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45;
lean_object* l_Lean_Server_handleLspRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__11(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24;
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51;
static lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__71;
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
extern lean_object* l_Lean_Server_Snapshots_instInhabitedSnapshot;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at_Lean_Server_FileWorker_initAndRunWorker___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDidChange(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4;
static lean_object* l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
lean_object* l_IO_FS_Stream_withPrefix(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4;
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_initSrcSearchPath___rarg(lean_object*, lean_object*);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcConnected____x40_Lean_Data_Lsp_Extra___hyg_1626_(uint64_t);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3;
lean_object* l_IO_AsyncList_waitHead_x3f___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__15;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_List_dropLast___rarg(lean_object*);
lean_object* l_IO_AsyncList_append___rarg(lean_object*, lean_object*);
lean_object* l_IO_throwServerError___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__14;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30;
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3___boxed(lean_object*, lean_object*);
extern lean_object* l_Task_Priority_dedicated;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43;
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__3;
static lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1;
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54;
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__4;
lean_object* l_IO_sleep(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__7(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_AsyncList_ofList___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleDidChange___closed__4;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Server_FileWorker_updateDocument___spec__2(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate___closed__1;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* l_Lean_Server_publishProgressAtPos(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39;
lean_object* l_List_toPArray_x27___rarg(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
lean_object* lean_get_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2;
lean_object* l_IO_AsyncList_getFinishedPrefix___rarg(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__8(uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22;
lean_object* l_String_firstDiffPos(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcKeepAliveParams____x40_Lean_Data_Lsp_Extra___hyg_2266_(lean_object*);
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_Lean_Elab_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Server_FileWorker_handleRequest___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
lean_object* lean_io_exit(uint8_t, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__67;
lean_object* l_Lean_Elab_headerToImports(lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__10;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_EIO_toBaseIO___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
static lean_object* l_Lean_Server_FileWorker_handleDidChange___closed__1;
lean_object* l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_126_(lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29;
static lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__1;
static lean_object* l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__2;
static lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams(lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
static uint8_t l_Lean_Server_FileWorker_handleDidChange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62;
lean_object* l_Lean_HashMap_toList___at_Lean_Server_ModuleRefs_instCoeModuleRefsModuleRefs___spec__1(lean_object*);
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toPArray_x27___rarg(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1412_(lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleNotification___closed__4;
lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Server_Snapshots_Snapshot_isAtEnd(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Server_rpcReleaseRef(size_t, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
static lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__69;
lean_object* l_Lean_Server_publishDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_load_dynlib(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6;
static lean_object* l_Lean_Server_FileWorker_initAndRunWorker___closed__4;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9;
lean_object* l_Lean_HashMap_ofList___at_Lean_Server_ModuleRefs_instCoeModuleRefsModuleRefs___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_mainLoop(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10;
lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_FileWorker_CancelToken_set(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_server_worker_main(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_toLspResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6;
static lean_object* l_Lean_Server_FileWorker_handleNotification___closed__5;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__74;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__8;
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__2(uint32_t, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__3;
lean_object* l_Lean_Server_FileWorker_RpcSession_new(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__1(size_t, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1;
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_202_(lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcConnectParams____x40_Lean_Data_Lsp_Extra___hyg_1446_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Server_FileWorker_updateDocument___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3(lean_object*);
lean_object* l_Lean_Lsp_InitializeParams_editDelay(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__65;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___rarg(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__4___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___closed__1;
lean_object* lean_task_get_own(lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__2;
lean_object* l_IO_ofExcept___at_IO_Process_output___spec__1(lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__68;
lean_object* l_Lean_PersistentArray_toArray___rarg(lean_object*);
static lean_object* l_Lean_Server_FileWorker_handleNotification___closed__3;
static lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3;
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2;
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
lean_object* l_IO_AsyncList_unfoldAsync___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_RefInfo_instCoeRefInfoRefInfo___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__1(size_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Server_RefInfo_instCoeRefInfoRefInfo___spec__1(x_13, x_1, x_11);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_6, 1, x_16);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
lean_ctor_set(x_10, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_32);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = l_Array_mapMUnsafe_map___at_Lean_Server_RefInfo_instCoeRefInfoRefInfo___spec__1(x_34, x_1, x_32);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_38);
{
lean_object* _tmp_1 = x_28;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_41 = x_31;
} else {
 lean_dec_ref(x_31);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_40, 2);
lean_inc(x_42);
lean_dec(x_40);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_35);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_45);
{
lean_object* _tmp_1 = x_28;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_2);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_array_get_size(x_53);
x_55 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_56 = l_Array_mapMUnsafe_map___at_Lean_Server_RefInfo_instCoeRefInfoRefInfo___spec__1(x_55, x_1, x_53);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
if (lean_is_scalar(x_51)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_51;
}
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_3);
x_2 = x_48;
x_3 = x_60;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_63 = x_52;
} else {
 lean_dec_ref(x_52);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_62, 2);
lean_inc(x_64);
lean_dec(x_62);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
if (lean_is_scalar(x_51)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_51;
}
lean_ctor_set(x_67, 0, x_49);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
x_2 = x_48;
x_3 = x_68;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected structured object, got '", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Internal_0__Lean_Lsp_toJsonLeanIleanInfoParams____x40_Lean_Data_Lsp_Internal___hyg_1412_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_IO_FS_Stream_writeLspMessage(x_1, x_9, x_3);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_handleDocumentHighlight___spec__1(x_7, x_8, x_4);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = 1;
x_12 = 0;
x_13 = l_Lean_Server_findModuleRefs(x_10, x_9, x_11, x_12);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_HashMap_toList___at_Lean_Server_ModuleRefs_instCoeModuleRefsModuleRefs___spec__1(x_13);
x_16 = lean_box(0);
x_17 = l_List_mapTR_loop___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__1(x_8, x_15, x_16);
x_18 = l_Lean_HashMap_ofList___at_Lean_Server_ModuleRefs_instCoeModuleRefsModuleRefs___spec__5(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_IO_FS_Stream_writeLspNotification___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__2(x_3, x_20, x_5);
return x_21;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = l_List_mapTR_loop___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__1(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/ileanInfoUpdate", 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate___closed__1;
x_6 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/ileanInfoFinal", 21);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal___closed__1;
x_6 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_st_ref_get(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = l_Lean_Server_Snapshots_Snapshot_endPos(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = 0;
lean_inc(x_10);
lean_inc(x_3);
x_12 = l_Lean_Server_publishProgressAtPos(x_3, x_9, x_10, x_11, x_8);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_3);
x_14 = l_Lean_Server_DocumentMeta_mkInputContext(x_3);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
lean_dec(x_2);
x_16 = l_Lean_Server_Snapshots_compileNextCmd(x_14, x_1, x_15, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = lean_array_push(x_4, x_17);
x_20 = l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1(x_5, x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
lean_inc(x_17);
x_26 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_17);
x_27 = l_Lean_PersistentArray_toArray___rarg(x_26);
lean_inc(x_10);
lean_inc(x_3);
x_28 = l_Lean_Server_publishDiagnostics(x_3, x_27, x_10, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
lean_inc(x_17);
x_31 = lean_array_push(x_30, x_17);
x_32 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate___closed__1;
x_33 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo(x_32, x_3, x_10, x_31, x_29);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_21, 0, x_36);
lean_ctor_set(x_33, 0, x_21);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_21, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_21);
lean_dec(x_24);
lean_dec(x_17);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_33, 0, x_42);
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_21);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_28);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_28, 0, x_49);
return x_28;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_28, 0);
x_51 = lean_ctor_get(x_28, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_28);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_dec(x_21);
lean_inc(x_17);
x_55 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_17);
x_56 = l_Lean_PersistentArray_toArray___rarg(x_55);
lean_inc(x_10);
lean_inc(x_3);
x_57 = l_Lean_Server_publishDiagnostics(x_3, x_56, x_10, x_22);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
lean_inc(x_17);
x_60 = lean_array_push(x_59, x_17);
x_61 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate___closed__1;
x_62 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo(x_61, x_3, x_10, x_60, x_58);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_17);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_54);
lean_dec(x_17);
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_68);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_54);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_3);
x_73 = lean_ctor_get(x_57, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_57, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_75 = x_57;
} else {
 lean_dec_ref(x_57);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_20);
if (x_78 == 0)
{
return x_20;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_20, 0);
x_80 = lean_ctor_get(x_20, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_20);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_16);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_16, 0);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_16, 0, x_84);
return x_16;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_16, 0);
x_86 = lean_ctor_get(x_16, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_16);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_85);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_12);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_12, 0);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_12, 0, x_91);
return x_12;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_12, 0);
x_93 = lean_ctor_get(x_12, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_12);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_92);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1(x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = l_Lean_Server_Snapshots_instInhabitedSnapshot;
x_13 = l_Array_back___rarg(x_12, x_10);
lean_inc(x_13);
x_14 = l_Lean_Server_Snapshots_Snapshot_isAtEnd(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_7);
x_15 = lean_box(0);
lean_inc(x_10);
x_16 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1(x_13, x_1, x_2, x_10, x_3, x_15, x_10, x_8);
lean_dec(x_3);
lean_dec(x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_17 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_13);
x_18 = l_Lean_PersistentArray_toArray___rarg(x_17);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_19);
lean_inc(x_2);
x_20 = l_Lean_Server_publishDiagnostics(x_2, x_18, x_19, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_19);
lean_inc(x_2);
x_22 = l_Lean_Server_publishProgressDone(x_2, x_19, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal___closed__1;
lean_inc(x_10);
x_25 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo(x_24, x_2, x_19, x_10, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_7, 0, x_28);
lean_ctor_set(x_25, 0, x_7);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
lean_ctor_set(x_7, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_7);
lean_dec(x_10);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_25, 0, x_34);
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_free_object(x_7);
lean_dec(x_10);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_22, 0, x_41);
return x_22;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_22, 0);
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_22);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_free_object(x_7);
lean_dec(x_10);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_20, 0, x_48);
return x_20;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_dec(x_7);
x_54 = l_Lean_Server_Snapshots_instInhabitedSnapshot;
x_55 = l_Array_back___rarg(x_54, x_53);
lean_inc(x_55);
x_56 = l_Lean_Server_Snapshots_Snapshot_isAtEnd(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_box(0);
lean_inc(x_53);
x_58 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1(x_55, x_1, x_2, x_53, x_3, x_57, x_53, x_8);
lean_dec(x_3);
lean_dec(x_53);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_3);
x_59 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_55);
x_60 = l_Lean_PersistentArray_toArray___rarg(x_59);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
lean_dec(x_1);
lean_inc(x_61);
lean_inc(x_2);
x_62 = l_Lean_Server_publishDiagnostics(x_2, x_60, x_61, x_8);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_61);
lean_inc(x_2);
x_64 = l_Lean_Server_publishProgressDone(x_2, x_61, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal___closed__1;
lean_inc(x_53);
x_67 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo(x_66, x_2, x_61, x_53, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_53);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_53);
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_75 = x_67;
} else {
 lean_dec_ref(x_67);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_61);
lean_dec(x_53);
lean_dec(x_2);
x_78 = lean_ctor_get(x_64, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_80 = x_64;
} else {
 lean_dec_ref(x_64);
 x_80 = lean_box(0);
}
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_78);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_61);
lean_dec(x_53);
lean_dec(x_2);
x_83 = lean_ctor_get(x_62, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_62, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_85 = x_62;
} else {
 lean_dec_ref(x_62);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_83);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_6);
if (x_88 == 0)
{
return x_6;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_6, 0);
x_90 = lean_ctor_get(x_6, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_6);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_CancelToken_check___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_unfoldCmdSnaps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_array_get_size(x_2);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_dec_lt(x_57, x_56);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = l_Lean_Server_Snapshots_instInhabitedSnapshot;
x_60 = l___private_Init_Util_0__outOfBounds___rarg(x_59);
x_6 = x_60;
goto block_55;
}
else
{
lean_object* x_61; 
x_61 = lean_array_fget(x_2, x_57);
x_6 = x_61;
goto block_55;
}
block_55:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_6);
x_8 = l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_11 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo(x_10, x_1, x_9, x_2, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap), 5, 3);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_3);
lean_inc(x_2);
x_14 = l_IO_AsyncList_unfoldAsync___rarg(x_13, x_2, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_array_to_list(lean_box(0), x_2);
x_18 = l_IO_AsyncList_ofList___rarg(x_17);
x_19 = l_IO_AsyncList_append___rarg(x_18, x_16);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_array_to_list(lean_box(0), x_2);
x_23 = l_IO_AsyncList_ofList___rarg(x_22);
x_24 = l_IO_AsyncList_append___rarg(x_23, x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_dec(x_4);
x_32 = 1;
lean_inc(x_31);
lean_inc(x_1);
x_33 = l_Lean_Server_publishProgressAtPos(x_1, x_30, x_31, x_32, x_5);
lean_dec(x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
lean_inc(x_6);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_38 = lean_array_push(x_37, x_6);
x_39 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal___closed__1;
x_40 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo(x_39, x_1, x_31, x_38, x_34);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_IO_AsyncList_ofList___rarg(x_36);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_IO_AsyncList_ofList___rarg(x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_36);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_33);
if (x_51 == 0)
{
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_33, 0);
x_53 = lean_ctor_get(x_33, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_33);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_io_prim_handle_get_line(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_dec_eq(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_9);
x_15 = lean_box(0);
x_16 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3;
x_17 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4;
x_18 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
lean_inc(x_11);
x_19 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_15);
lean_ctor_set(x_19, 5, x_11);
lean_ctor_set(x_19, 6, x_15);
lean_ctor_set(x_19, 7, x_15);
lean_ctor_set(x_19, 8, x_15);
x_20 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_21 = lean_array_push(x_20, x_19);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_Server_publishDiagnostics(x_2, x_21, x_3, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_string_append(x_6, x_11);
lean_dec(x_11);
x_6 = x_24;
x_7 = x_23;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_33 = lean_string_dec_eq(x_30, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_box(0);
x_35 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3;
x_36 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4;
x_37 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5;
lean_inc(x_30);
x_38 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set(x_38, 4, x_34);
lean_ctor_set(x_38, 5, x_30);
lean_ctor_set(x_38, 6, x_34);
lean_ctor_set(x_38, 7, x_34);
lean_ctor_set(x_38, 8, x_34);
x_39 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_40 = lean_array_push(x_39, x_38);
lean_inc(x_3);
lean_inc(x_2);
x_41 = l_Lean_Server_publishDiagnostics(x_2, x_40, x_3, x_31);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_string_append(x_6, x_30);
lean_dec(x_30);
x_6 = x_43;
x_7 = x_42;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_47 = x_41;
} else {
 lean_dec_ref(x_41);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_6);
lean_ctor_set(x_49, 1, x_31);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_9);
if (x_50 == 0)
{
return x_9;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_9, 0);
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_9);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_reverse___rarg(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_realPathNormalized(x_7, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_11;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
uint8_t x_13; 
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = l_Lean_realPathNormalized(x_17, x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_2);
x_1 = x_18;
x_2 = x_22;
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
lean_dec(x_2);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_26 = x_19;
} else {
 lean_dec_ref(x_19);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_load_dynlib(x_7, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("print-paths", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_2 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 2;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_2);
lean_ctor_set_uint8(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` failed:\n", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nstderr:\n", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid output from `", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`:\n", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_lakeSetupSearchPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1(x_7, x_8, x_3);
x_10 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2;
x_11 = l_Array_append___rarg(x_10, x_9);
lean_inc(x_11);
x_12 = lean_array_to_list(lean_box(0), x_11);
lean_inc(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3;
x_15 = l_String_intercalate(x_14, x_13);
x_16 = lean_box(0);
x_17 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4;
x_18 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5;
lean_inc(x_11);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_18);
x_20 = lean_io_process_spawn(x_19, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
lean_inc(x_21);
x_24 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___boxed), 7, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_4);
lean_closure_set(x_24, 3, x_11);
lean_closure_set(x_24, 4, x_21);
lean_closure_set(x_24, 5, x_23);
x_25 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = l_Task_Priority_dedicated;
x_27 = lean_io_as_task(x_25, x_26, x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
x_31 = l_IO_FS_Handle_readToEnd_loop(x_30, x_23, x_29);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_String_trim(x_32);
lean_dec(x_32);
x_35 = lean_task_get_own(x_28);
x_36 = l_IO_ofExcept___at_IO_Process_output___spec__1(x_35, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_io_process_child_wait(x_17, x_21, x_38);
lean_dec(x_21);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint32_t x_43; uint32_t x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = 0;
x_44 = lean_unbox_uint32(x_41);
x_45 = lean_uint32_dec_eq(x_44, x_43);
if (x_45 == 0)
{
uint32_t x_46; uint32_t x_47; uint8_t x_48; 
x_46 = 2;
x_47 = lean_unbox_uint32(x_41);
lean_dec(x_41);
x_48 = lean_uint32_dec_eq(x_47, x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_39);
x_49 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6;
x_50 = lean_string_append(x_49, x_15);
lean_dec(x_15);
x_51 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_string_append(x_52, x_34);
lean_dec(x_34);
x_54 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_string_append(x_55, x_37);
lean_dec(x_37);
x_57 = lean_string_append(x_56, x_23);
x_58 = l_IO_throwServerError___rarg(x_57, x_42);
return x_58;
}
else
{
lean_object* x_59; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_15);
x_59 = lean_box(0);
lean_ctor_set(x_39, 0, x_59);
return x_39;
}
}
else
{
lean_object* x_60; 
lean_free_object(x_39);
lean_dec(x_41);
lean_inc(x_34);
x_60 = l_Lean_Json_parse(x_34);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_60);
x_61 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9;
x_62 = lean_string_append(x_61, x_15);
lean_dec(x_15);
x_63 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_34);
lean_dec(x_34);
x_66 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_37);
lean_dec(x_37);
x_69 = lean_string_append(x_68, x_23);
x_70 = l_IO_throwServerError___rarg(x_69, x_42);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
lean_dec(x_60);
x_72 = l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_126_(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_72);
x_73 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9;
x_74 = lean_string_append(x_73, x_15);
lean_dec(x_15);
x_75 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10;
x_76 = lean_string_append(x_74, x_75);
x_77 = lean_string_append(x_76, x_34);
lean_dec(x_34);
x_78 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_79 = lean_string_append(x_77, x_78);
x_80 = lean_string_append(x_79, x_37);
lean_dec(x_37);
x_81 = lean_string_append(x_80, x_23);
x_82 = l_IO_throwServerError___rarg(x_81, x_42);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_15);
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
lean_dec(x_72);
x_84 = lean_get_prefix(x_42);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
x_88 = l_Lean_initSearchPath(x_85, x_87, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get(x_83, 2);
lean_inc(x_90);
x_91 = lean_array_get_size(x_90);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_nat_dec_lt(x_92, x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_91);
lean_dec(x_90);
x_94 = lean_ctor_get(x_83, 1);
lean_inc(x_94);
lean_dec(x_83);
x_95 = lean_box(0);
x_96 = l_List_mapM_loop___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(x_94, x_95, x_89);
return x_96;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_91, x_91);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_91);
lean_dec(x_90);
x_98 = lean_ctor_get(x_83, 1);
lean_inc(x_98);
lean_dec(x_83);
x_99 = lean_box(0);
x_100 = l_List_mapM_loop___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(x_98, x_99, x_89);
return x_100;
}
else
{
size_t x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_102 = lean_box(0);
x_103 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__3(x_90, x_8, x_101, x_102, x_89);
lean_dec(x_90);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_83, 1);
lean_inc(x_105);
lean_dec(x_83);
x_106 = lean_box(0);
x_107 = l_List_mapM_loop___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(x_105, x_106, x_104);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_83);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
return x_103;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_103, 0);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_103);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_83);
x_112 = !lean_is_exclusive(x_88);
if (x_112 == 0)
{
return x_88;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_88, 0);
x_114 = lean_ctor_get(x_88, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_88);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_83);
x_116 = !lean_is_exclusive(x_84);
if (x_116 == 0)
{
return x_84;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_84, 0);
x_118 = lean_ctor_get(x_84, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_84);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint32_t x_122; uint32_t x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_39, 0);
x_121 = lean_ctor_get(x_39, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_39);
x_122 = 0;
x_123 = lean_unbox_uint32(x_120);
x_124 = lean_uint32_dec_eq(x_123, x_122);
if (x_124 == 0)
{
uint32_t x_125; uint32_t x_126; uint8_t x_127; 
x_125 = 2;
x_126 = lean_unbox_uint32(x_120);
lean_dec(x_120);
x_127 = lean_uint32_dec_eq(x_126, x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_128 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6;
x_129 = lean_string_append(x_128, x_15);
lean_dec(x_15);
x_130 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7;
x_131 = lean_string_append(x_129, x_130);
x_132 = lean_string_append(x_131, x_34);
lean_dec(x_34);
x_133 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_134 = lean_string_append(x_132, x_133);
x_135 = lean_string_append(x_134, x_37);
lean_dec(x_37);
x_136 = lean_string_append(x_135, x_23);
x_137 = l_IO_throwServerError___rarg(x_136, x_121);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_15);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_121);
return x_139;
}
}
else
{
lean_object* x_140; 
lean_dec(x_120);
lean_inc(x_34);
x_140 = l_Lean_Json_parse(x_34);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_140);
x_141 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9;
x_142 = lean_string_append(x_141, x_15);
lean_dec(x_15);
x_143 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_string_append(x_144, x_34);
lean_dec(x_34);
x_146 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_147 = lean_string_append(x_145, x_146);
x_148 = lean_string_append(x_147, x_37);
lean_dec(x_37);
x_149 = lean_string_append(x_148, x_23);
x_150 = l_IO_throwServerError___rarg(x_149, x_121);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_140, 0);
lean_inc(x_151);
lean_dec(x_140);
x_152 = l___private_Lean_Util_Paths_0__Lean_fromJsonLeanPaths____x40_Lean_Util_Paths___hyg_126_(x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_152);
x_153 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9;
x_154 = lean_string_append(x_153, x_15);
lean_dec(x_15);
x_155 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10;
x_156 = lean_string_append(x_154, x_155);
x_157 = lean_string_append(x_156, x_34);
lean_dec(x_34);
x_158 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8;
x_159 = lean_string_append(x_157, x_158);
x_160 = lean_string_append(x_159, x_37);
lean_dec(x_37);
x_161 = lean_string_append(x_160, x_23);
x_162 = l_IO_throwServerError___rarg(x_161, x_121);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_15);
x_163 = lean_ctor_get(x_152, 0);
lean_inc(x_163);
lean_dec(x_152);
x_164 = lean_get_prefix(x_121);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_163, 0);
lean_inc(x_167);
x_168 = l_Lean_initSearchPath(x_165, x_167, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_ctor_get(x_163, 2);
lean_inc(x_170);
x_171 = lean_array_get_size(x_170);
x_172 = lean_unsigned_to_nat(0u);
x_173 = lean_nat_dec_lt(x_172, x_171);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_171);
lean_dec(x_170);
x_174 = lean_ctor_get(x_163, 1);
lean_inc(x_174);
lean_dec(x_163);
x_175 = lean_box(0);
x_176 = l_List_mapM_loop___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(x_174, x_175, x_169);
return x_176;
}
else
{
uint8_t x_177; 
x_177 = lean_nat_dec_le(x_171, x_171);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_171);
lean_dec(x_170);
x_178 = lean_ctor_get(x_163, 1);
lean_inc(x_178);
lean_dec(x_163);
x_179 = lean_box(0);
x_180 = l_List_mapM_loop___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(x_178, x_179, x_169);
return x_180;
}
else
{
size_t x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_usize_of_nat(x_171);
lean_dec(x_171);
x_182 = lean_box(0);
x_183 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__3(x_170, x_8, x_181, x_182, x_169);
lean_dec(x_170);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_ctor_get(x_163, 1);
lean_inc(x_185);
lean_dec(x_163);
x_186 = lean_box(0);
x_187 = l_List_mapM_loop___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__2(x_185, x_186, x_184);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_163);
x_188 = lean_ctor_get(x_183, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_183, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_190 = x_183;
} else {
 lean_dec_ref(x_183);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_163);
x_192 = lean_ctor_get(x_168, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_168, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_194 = x_168;
} else {
 lean_dec_ref(x_168);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_163);
x_196 = lean_ctor_get(x_164, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_164, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_198 = x_164;
} else {
 lean_dec_ref(x_164);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_15);
x_200 = !lean_is_exclusive(x_39);
if (x_200 == 0)
{
return x_39;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_39, 0);
x_202 = lean_ctor_get(x_39, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_39);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_34);
lean_dec(x_21);
lean_dec(x_15);
x_204 = !lean_is_exclusive(x_36);
if (x_204 == 0)
{
return x_36;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_36, 0);
x_206 = lean_ctor_get(x_36, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_36);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_15);
x_208 = !lean_is_exclusive(x_31);
if (x_208 == 0)
{
return x_31;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_31, 0);
x_210 = lean_ctor_get(x_31, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_31);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_20);
if (x_212 == 0)
{
return x_20;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_20, 0);
x_214 = lean_ctor_get(x_20, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_20);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Server_FileWorker_lakeSetupSearchPath___spec__3(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("import", 6);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5;
x_2 = l_Array_toPArray_x27___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__3;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__2;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__3;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_1 = x_14;
x_2 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_9 = lean_array_uget(x_5, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
lean_inc(x_2);
x_12 = l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__3(x_1, x_2, x_9, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = lean_array_uset(x_11, x_4, x_13);
x_4 = x_16;
x_5 = x_17;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_9 = lean_array_uget(x_5, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
lean_inc(x_2);
x_12 = l_Lean_Widget_msgToInteractiveDiagnostic(x_2, x_9, x_1, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = lean_array_uset(x_11, x_4, x_13);
x_4 = x_16;
x_5 = x_17;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4(x_1, x_2, x_8, x_9, x_6, x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_3, 0, x_12);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_3, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4(x_1, x_2, x_18, x_19, x_16, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_array_get_size(x_27);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5(x_1, x_2, x_29, x_30, x_27, x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_ctor_set(x_3, 0, x_33);
lean_ctor_set(x_31, 0, x_3);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
lean_ctor_set(x_3, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
lean_dec(x_3);
x_38 = lean_array_get_size(x_37);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = 0;
x_41 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5(x_1, x_2, x_39, x_40, x_37, x_4);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__6(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_9 = lean_array_uget(x_5, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
lean_inc(x_2);
x_12 = l_Lean_Widget_msgToInteractiveDiagnostic(x_2, x_9, x_1, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = lean_array_uset(x_11, x_4, x_13);
x_4 = x_16;
x_5 = x_17;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
x_8 = l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__3(x_1, x_2, x_6, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_get_size(x_7);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__6(x_1, x_2, x_12, x_13, x_7, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_9);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_ctor_get_usize(x_3, 4);
x_24 = lean_ctor_get(x_3, 3);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
lean_inc(x_2);
x_25 = l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__3(x_1, x_2, x_20, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_get_size(x_21);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__6(x_1, x_2, x_29, x_30, x_21, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_22);
lean_ctor_set(x_35, 3, x_24);
lean_ctor_set_usize(x_35, 4, x_23);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_9 = lean_array_uget(x_5, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
lean_inc(x_2);
x_12 = l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__8(x_1, x_2, x_9, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = lean_array_uset(x_11, x_4, x_13);
x_4 = x_16;
x_5 = x_17;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_9 = lean_array_uget(x_5, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
lean_inc(x_2);
x_12 = l_Lean_Widget_msgToInteractiveDiagnostic(x_2, x_9, x_1, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = lean_array_uset(x_11, x_4, x_13);
x_4 = x_16;
x_5 = x_17;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__8(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9(x_1, x_2, x_8, x_9, x_6, x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_3, 0, x_12);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_3, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9(x_1, x_2, x_18, x_19, x_16, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_array_get_size(x_27);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10(x_1, x_2, x_29, x_30, x_27, x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_ctor_set(x_3, 0, x_33);
lean_ctor_set(x_31, 0, x_3);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
lean_ctor_set(x_3, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
lean_dec(x_3);
x_38 = lean_array_get_size(x_37);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = 0;
x_41 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10(x_1, x_2, x_39, x_40, x_37, x_4);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__11(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_4, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_9 = lean_array_uget(x_5, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
lean_inc(x_2);
x_12 = l_Lean_Widget_msgToInteractiveDiagnostic(x_2, x_9, x_1, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_17 = lean_array_uset(x_11, x_4, x_13);
x_4 = x_16;
x_5 = x_17;
x_6 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__7(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
x_8 = l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__8(x_1, x_2, x_6, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_get_size(x_7);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__11(x_1, x_2, x_12, x_13, x_7, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_9);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_ctor_get_usize(x_3, 4);
x_24 = lean_ctor_get(x_3, 3);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
lean_inc(x_2);
x_25 = l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__8(x_1, x_2, x_20, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_get_size(x_21);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__11(x_1, x_2, x_29, x_30, x_21, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_22);
lean_ctor_set(x_35, 3, x_24);
lean_ctor_set_usize(x_35, 4, x_23);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_firstFrontendMacroScope;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6;
x_3 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5;
x_4 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_worker", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__10;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("header", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__14;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_122; lean_object* x_123; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_13 = x_9;
} else {
 lean_dec_ref(x_9);
 x_13 = lean_box(0);
}
x_122 = lean_ctor_get(x_2, 0);
lean_inc(x_122);
x_123 = l_System_Uri_fileUriToPath_x3f(x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; uint8_t x_125; 
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
x_124 = l_Lean_Elab_Command_mkState(x_11, x_12, x_1);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_126 = lean_ctor_get(x_124, 7);
lean_dec(x_126);
x_127 = lean_ctor_get(x_124, 5);
lean_dec(x_127);
x_128 = lean_ctor_get(x_124, 4);
lean_dec(x_128);
x_129 = lean_ctor_get(x_124, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_124, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_124, 0);
lean_dec(x_131);
x_132 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2;
x_133 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_1, x_132);
lean_dec(x_1);
x_134 = lean_ctor_get(x_2, 2);
lean_inc(x_134);
x_135 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__8;
x_136 = lean_box(0);
x_137 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__11;
lean_inc_n(x_3, 2);
lean_inc(x_134);
lean_inc(x_11);
x_138 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_138, 0, x_11);
lean_ctor_set(x_138, 1, x_134);
lean_ctor_set(x_138, 2, x_135);
lean_ctor_set(x_138, 3, x_3);
lean_ctor_set(x_138, 4, x_136);
lean_ctor_set(x_138, 5, x_3);
lean_ctor_set(x_138, 6, x_137);
x_139 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__13;
lean_inc(x_4);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_4);
x_141 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = lean_unsigned_to_nat(1u);
x_143 = l_Lean_Syntax_getArg(x_4, x_142);
x_144 = l_Lean_Syntax_getArgs(x_143);
lean_dec(x_143);
x_145 = lean_array_to_list(lean_box(0), x_144);
x_146 = l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1(x_145, x_3);
x_147 = l_List_toPArray_x27___rarg(x_146);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_138);
lean_ctor_set(x_149, 1, x_148);
x_150 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_151 = lean_array_push(x_150, x_149);
x_152 = l_Array_toPArray_x27___rarg(x_151);
lean_dec(x_151);
x_153 = 1;
x_154 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5;
x_155 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_152);
lean_ctor_set_uint8(x_155, sizeof(void*)*2, x_153);
x_156 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1;
lean_inc(x_12);
lean_ctor_set(x_124, 7, x_155);
lean_ctor_set(x_124, 5, x_142);
lean_ctor_set(x_124, 4, x_133);
lean_ctor_set(x_124, 3, x_156);
lean_ctor_set(x_124, 1, x_12);
lean_ctor_set(x_124, 0, x_11);
x_157 = l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__7(x_5, x_134, x_12, x_10);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__15;
x_161 = lean_st_mk_ref(x_160, x_159);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_unsigned_to_nat(0u);
x_165 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_4);
lean_ctor_set(x_165, 2, x_6);
lean_ctor_set(x_165, 3, x_124);
lean_ctor_set(x_165, 4, x_158);
lean_ctor_set(x_165, 5, x_162);
lean_inc(x_165);
x_166 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_165);
x_167 = l_Lean_PersistentArray_toArray___rarg(x_166);
x_168 = l_Lean_Server_publishDiagnostics(x_2, x_167, x_7, x_163);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_168, 0);
lean_dec(x_170);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_8);
lean_ctor_set(x_168, 0, x_171);
return x_168;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
lean_dec(x_168);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_165);
lean_ctor_set(x_173, 1, x_8);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
uint8_t x_175; 
lean_dec(x_165);
lean_dec(x_8);
x_175 = !lean_is_exclusive(x_168);
if (x_175 == 0)
{
return x_168;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_168, 0);
x_177 = lean_ctor_get(x_168, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_168);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_179 = lean_ctor_get(x_124, 2);
x_180 = lean_ctor_get(x_124, 6);
x_181 = lean_ctor_get(x_124, 8);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_124);
x_182 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2;
x_183 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_1, x_182);
lean_dec(x_1);
x_184 = lean_ctor_get(x_2, 2);
lean_inc(x_184);
x_185 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__8;
x_186 = lean_box(0);
x_187 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__11;
lean_inc_n(x_3, 2);
lean_inc(x_184);
lean_inc(x_11);
x_188 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_188, 0, x_11);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_185);
lean_ctor_set(x_188, 3, x_3);
lean_ctor_set(x_188, 4, x_186);
lean_ctor_set(x_188, 5, x_3);
lean_ctor_set(x_188, 6, x_187);
x_189 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__13;
lean_inc(x_4);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_4);
x_191 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_unsigned_to_nat(1u);
x_193 = l_Lean_Syntax_getArg(x_4, x_192);
x_194 = l_Lean_Syntax_getArgs(x_193);
lean_dec(x_193);
x_195 = lean_array_to_list(lean_box(0), x_194);
x_196 = l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1(x_195, x_3);
x_197 = l_List_toPArray_x27___rarg(x_196);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_191);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_188);
lean_ctor_set(x_199, 1, x_198);
x_200 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_201 = lean_array_push(x_200, x_199);
x_202 = l_Array_toPArray_x27___rarg(x_201);
lean_dec(x_201);
x_203 = 1;
x_204 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5;
x_205 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
lean_ctor_set_uint8(x_205, sizeof(void*)*2, x_203);
x_206 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1;
lean_inc(x_12);
x_207 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_207, 0, x_11);
lean_ctor_set(x_207, 1, x_12);
lean_ctor_set(x_207, 2, x_179);
lean_ctor_set(x_207, 3, x_206);
lean_ctor_set(x_207, 4, x_183);
lean_ctor_set(x_207, 5, x_192);
lean_ctor_set(x_207, 6, x_180);
lean_ctor_set(x_207, 7, x_205);
lean_ctor_set(x_207, 8, x_181);
x_208 = l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__7(x_5, x_184, x_12, x_10);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__15;
x_212 = lean_st_mk_ref(x_211, x_210);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_unsigned_to_nat(0u);
x_216 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_4);
lean_ctor_set(x_216, 2, x_6);
lean_ctor_set(x_216, 3, x_207);
lean_ctor_set(x_216, 4, x_209);
lean_ctor_set(x_216, 5, x_213);
lean_inc(x_216);
x_217 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_216);
x_218 = l_Lean_PersistentArray_toArray___rarg(x_217);
x_219 = l_Lean_Server_publishDiagnostics(x_2, x_218, x_7, x_214);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_216);
lean_ctor_set(x_222, 1, x_8);
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_220);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_216);
lean_dec(x_8);
x_224 = lean_ctor_get(x_219, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_219, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_226 = x_219;
} else {
 lean_dec_ref(x_219);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_123, 0);
lean_inc(x_228);
lean_dec(x_123);
x_229 = lean_box(0);
x_230 = lean_module_name_of_file(x_228, x_229, x_10);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_environment_set_main_module(x_11, x_231);
x_234 = lean_box(0);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_14 = x_235;
x_15 = x_232;
goto block_121;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_230, 1);
lean_inc(x_236);
lean_dec(x_230);
x_237 = lean_box(0);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_11);
x_14 = x_238;
x_15 = x_236;
goto block_121;
}
}
block_121:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_16);
x_17 = l_Lean_Elab_Command_mkState(x_16, x_12, x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_19 = lean_ctor_get(x_17, 7);
lean_dec(x_19);
x_20 = lean_ctor_get(x_17, 5);
lean_dec(x_20);
x_21 = lean_ctor_get(x_17, 4);
lean_dec(x_21);
x_22 = lean_ctor_get(x_17, 3);
lean_dec(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_17, 0);
lean_dec(x_24);
x_25 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2;
x_26 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_1, x_25);
lean_dec(x_1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
x_28 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__8;
x_29 = lean_box(0);
x_30 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__11;
lean_inc_n(x_3, 2);
lean_inc(x_27);
lean_inc(x_16);
x_31 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_3);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set(x_31, 5, x_3);
lean_ctor_set(x_31, 6, x_30);
x_32 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__13;
lean_inc(x_4);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Lean_Syntax_getArg(x_4, x_35);
x_37 = l_Lean_Syntax_getArgs(x_36);
lean_dec(x_36);
x_38 = lean_array_to_list(lean_box(0), x_37);
x_39 = l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1(x_38, x_3);
x_40 = l_List_toPArray_x27___rarg(x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_44 = lean_array_push(x_43, x_42);
x_45 = l_Array_toPArray_x27___rarg(x_44);
lean_dec(x_44);
x_46 = 1;
x_47 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5;
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_46);
x_49 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1;
lean_inc(x_12);
lean_ctor_set(x_17, 7, x_48);
lean_ctor_set(x_17, 5, x_35);
lean_ctor_set(x_17, 4, x_26);
lean_ctor_set(x_17, 3, x_49);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 0, x_16);
x_50 = l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__2(x_5, x_27, x_12, x_15);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__15;
x_54 = lean_st_mk_ref(x_53, x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_4);
lean_ctor_set(x_58, 2, x_6);
lean_ctor_set(x_58, 3, x_17);
lean_ctor_set(x_58, 4, x_51);
lean_ctor_set(x_58, 5, x_55);
lean_inc(x_58);
x_59 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_58);
x_60 = l_Lean_PersistentArray_toArray___rarg(x_59);
x_61 = l_Lean_Server_publishDiagnostics(x_2, x_60, x_7, x_56);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
if (lean_is_scalar(x_13)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_13;
}
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_8);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
if (lean_is_scalar(x_13)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_13;
}
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_8);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_58);
lean_dec(x_13);
lean_dec(x_8);
x_68 = !lean_is_exclusive(x_61);
if (x_68 == 0)
{
return x_61;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_61, 0);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_61);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_72 = lean_ctor_get(x_17, 2);
x_73 = lean_ctor_get(x_17, 6);
x_74 = lean_ctor_get(x_17, 8);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_17);
x_75 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2;
x_76 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_1, x_75);
lean_dec(x_1);
x_77 = lean_ctor_get(x_2, 2);
lean_inc(x_77);
x_78 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__8;
x_79 = lean_box(0);
x_80 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__11;
lean_inc_n(x_3, 2);
lean_inc(x_77);
lean_inc(x_16);
x_81 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_81, 0, x_16);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_3);
lean_ctor_set(x_81, 4, x_79);
lean_ctor_set(x_81, 5, x_3);
lean_ctor_set(x_81, 6, x_80);
x_82 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__13;
lean_inc(x_4);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_4);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_unsigned_to_nat(1u);
x_86 = l_Lean_Syntax_getArg(x_4, x_85);
x_87 = l_Lean_Syntax_getArgs(x_86);
lean_dec(x_86);
x_88 = lean_array_to_list(lean_box(0), x_87);
x_89 = l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1(x_88, x_3);
x_90 = l_List_toPArray_x27___rarg(x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set(x_92, 1, x_91);
x_93 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_94 = lean_array_push(x_93, x_92);
x_95 = l_Array_toPArray_x27___rarg(x_94);
lean_dec(x_94);
x_96 = 1;
x_97 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5;
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_96);
x_99 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1;
lean_inc(x_12);
x_100 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_100, 0, x_16);
lean_ctor_set(x_100, 1, x_12);
lean_ctor_set(x_100, 2, x_72);
lean_ctor_set(x_100, 3, x_99);
lean_ctor_set(x_100, 4, x_76);
lean_ctor_set(x_100, 5, x_85);
lean_ctor_set(x_100, 6, x_73);
lean_ctor_set(x_100, 7, x_98);
lean_ctor_set(x_100, 8, x_74);
x_101 = l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__2(x_5, x_77, x_12, x_15);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__15;
x_105 = lean_st_mk_ref(x_104, x_103);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_4);
lean_ctor_set(x_109, 2, x_6);
lean_ctor_set(x_109, 3, x_100);
lean_ctor_set(x_109, 4, x_102);
lean_ctor_set(x_109, 5, x_106);
lean_inc(x_109);
x_110 = l_Lean_Server_Snapshots_Snapshot_diagnostics(x_109);
x_111 = l_Lean_PersistentArray_toArray___rarg(x_110);
x_112 = l_Lean_Server_publishDiagnostics(x_2, x_111, x_7, x_107);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_13;
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_8);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_109);
lean_dec(x_13);
lean_dec(x_8);
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint32_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_Elab_processHeader(x_1, x_2, x_3, x_4, x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<ignored>", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lakefile.lean", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = l_System_Uri_fileUriToPath_x3f(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_11);
x_39 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
x_40 = l_Lean_Server_FileWorker_compileHeader___lambda__2(x_4, x_1, x_8, x_9, x_10, x_39, x_12);
lean_dec(x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_Server_FileWorker_compileHeader___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_43, x_44, x_42);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
x_13 = x_46;
x_14 = x_47;
goto block_36;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = l_System_FilePath_pathExists(x_11, x_12);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_System_FilePath_fileName(x_48);
x_53 = l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__4;
x_54 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1116____at_Lean_SearchPath_findAllWithExt___spec__1(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = lean_unbox(x_50);
lean_dec(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_11);
x_56 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
x_57 = l_Lean_Server_FileWorker_compileHeader___lambda__2(x_4, x_1, x_8, x_9, x_10, x_56, x_51);
lean_dec(x_9);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_10);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
x_62 = l_Lean_Server_FileWorker_compileHeader___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_60, x_61, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_13 = x_63;
x_14 = x_64;
goto block_36;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = l_Lean_Elab_headerToImports(x_4);
x_66 = l_List_redLength___rarg(x_65);
x_67 = lean_mk_empty_array_with_capacity(x_66);
lean_dec(x_66);
x_68 = l_List_toArrayAux___rarg(x_65, x_67);
lean_inc(x_7);
lean_inc(x_2);
x_69 = l_Lean_Server_FileWorker_lakeSetupSearchPath(x_11, x_2, x_68, x_7, x_51);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_get_prefix(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_initSrcSearchPath___rarg(x_70, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_box(0);
lean_inc(x_1);
x_78 = l_Lean_Server_FileWorker_compileHeader___lambda__2(x_4, x_1, x_8, x_9, x_75, x_77, x_76);
lean_dec(x_9);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_10);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec(x_79);
x_83 = l_Lean_Server_FileWorker_compileHeader___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_81, x_82, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_13 = x_84;
x_14 = x_85;
goto block_36;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_9);
lean_dec(x_8);
x_86 = lean_ctor_get(x_74, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_74, 1);
lean_inc(x_87);
lean_dec(x_74);
x_13 = x_86;
x_14 = x_87;
goto block_36;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_70);
lean_dec(x_9);
lean_dec(x_8);
x_88 = lean_ctor_get(x_72, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_dec(x_72);
x_13 = x_88;
x_14 = x_89;
goto block_36;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_9);
lean_dec(x_8);
x_90 = lean_ctor_get(x_69, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_69, 1);
lean_inc(x_91);
lean_dec(x_69);
x_13 = x_90;
x_14 = x_91;
goto block_36;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_50);
lean_dec(x_11);
x_92 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
x_93 = l_Lean_Server_FileWorker_compileHeader___lambda__2(x_4, x_1, x_8, x_9, x_10, x_92, x_51);
lean_dec(x_9);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_10);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
lean_dec(x_94);
x_98 = l_Lean_Server_FileWorker_compileHeader___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_96, x_97, x_95);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
x_13 = x_99;
x_14 = x_100;
goto block_36;
}
}
}
block_36:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; lean_object* x_27; 
x_15 = lean_box(0);
x_16 = lean_io_error_to_string(x_13);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__2;
x_20 = l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1;
x_21 = 2;
x_22 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_23 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_21);
x_24 = l_Lean_MessageLog_empty;
x_25 = l_Lean_PersistentArray_push___rarg(x_24, x_23);
x_26 = 0;
x_27 = lean_mk_empty_environment(x_26, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_25);
x_31 = l_Lean_Server_FileWorker_compileHeader___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_30, x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_System_FilePath_exeExtension;
x_6 = l_System_FilePath_withExtension(x_3, x_5);
x_7 = lean_apply_3(x_1, x_2, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LAKE", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LEAN_SYSROOT", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lake", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("bin", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_initSrcSearchPath___rarg(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1;
x_16 = lean_io_getenv(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(x_4);
x_20 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_compileHeader___lambda__3___boxed), 12, 9);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_11);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_19);
lean_closure_set(x_20, 5, x_5);
lean_closure_set(x_20, 6, x_6);
lean_closure_set(x_20, 7, x_7);
lean_closure_set(x_20, 8, x_8);
x_21 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2;
x_22 = lean_io_getenv(x_21, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_IO_appDir(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3;
x_29 = l_System_FilePath_join(x_26, x_28);
x_30 = l_Lean_Server_FileWorker_compileHeader___lambda__4(x_20, x_13, x_29, x_27);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_13);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4;
x_38 = l_System_FilePath_join(x_36, x_37);
x_39 = l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3;
x_40 = l_System_FilePath_join(x_38, x_39);
x_41 = l_Lean_Server_FileWorker_compileHeader___lambda__4(x_20, x_13, x_40, x_35);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_dec(x_16);
x_43 = lean_ctor_get(x_17, 0);
lean_inc(x_43);
lean_dec(x_17);
x_44 = l_Lean_Server_FileWorker_compileHeader___lambda__3(x_1, x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_13, x_43, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_12);
if (x_45 == 0)
{
return x_12;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_12, 0);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_12);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_compileHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_get_prefix), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = l_Lean_Server_DocumentMeta_mkInputContext(x_1);
lean_inc(x_6);
x_7 = l_Lean_Parser_parseHeader(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_box(x_4);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_compileHeader___lambda__5___boxed), 10, 8);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_11);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_13);
lean_closure_set(x_16, 5, x_2);
lean_closure_set(x_16, 6, x_14);
lean_closure_set(x_16, 7, x_6);
x_17 = l_Lean_Server_FileWorker_compileHeader___closed__1;
x_18 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_16);
x_19 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Task_Priority_default;
x_21 = lean_io_as_task(x_19, x_20, x_10);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_9, 1, x_23);
lean_ctor_set(x_9, 0, x_11);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_9, 1, x_24);
lean_ctor_set(x_9, 0, x_11);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_box(x_4);
lean_inc(x_11);
x_30 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_compileHeader___lambda__5___boxed), 10, 8);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_1);
lean_closure_set(x_30, 2, x_11);
lean_closure_set(x_30, 3, x_29);
lean_closure_set(x_30, 4, x_27);
lean_closure_set(x_30, 5, x_2);
lean_closure_set(x_30, 6, x_28);
lean_closure_set(x_30, 7, x_6);
x_31 = l_Lean_Server_FileWorker_compileHeader___closed__1;
x_32 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_32, 0, x_31);
lean_closure_set(x_32, 1, x_30);
x_33 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = l_Task_Priority_default;
x_35 = lean_io_as_task(x_33, x_34, x_10);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
return x_7;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__4(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__5(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__3(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__6(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__2(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__9(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__10(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentArray_mapMAux___at_Lean_Server_FileWorker_compileHeader___spec__8(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_compileHeader___spec__11(x_7, x_2, x_8, x_9, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentArray_mapM___at_Lean_Server_FileWorker_compileHeader___spec__7(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Server_FileWorker_compileHeader___lambda__1(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_compileHeader___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Server_FileWorker_compileHeader___lambda__3(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Server_FileWorker_compileHeader___lambda__5(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_compileHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Server_FileWorker_compileHeader(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_4, 0, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_18 = lean_array_push(x_17, x_16);
x_19 = l_Lean_Server_FileWorker_unfoldCmdSnaps(x_1, x_18, x_2, x_3, x_5);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_4, 0, x_21);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_4, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_27);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_35 = lean_array_push(x_34, x_33);
x_36 = l_Lean_Server_FileWorker_unfoldCmdSnaps(x_1, x_35, x_2, x_3, x_5);
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
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
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
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initializeWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_58; 
x_58 = lean_ctor_get(x_5, 3);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = 0;
x_8 = x_59;
goto block_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = 0;
x_8 = x_62;
goto block_57;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
x_8 = x_64;
goto block_57;
}
}
block_57:
{
lean_object* x_9; 
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Server_FileWorker_compileHeader(x_1, x_3, x_6, x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
x_15 = l_Lean_Server_FileWorker_CancelToken_new(x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_14);
x_18 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_4);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_8);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_initializeWorker___lambda__1), 5, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_16);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Task_Priority_default;
x_21 = lean_io_map_task(x_19, x_14, x_20, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_16);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_13);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_10, 1, x_27);
lean_ctor_set(x_10, 0, x_18);
lean_ctor_set(x_21, 0, x_10);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_16);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_13);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_18);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = l_Lean_Server_FileWorker_CancelToken_new(x_11);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_36);
x_40 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_3);
lean_ctor_set(x_40, 2, x_4);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_8);
lean_inc(x_40);
lean_inc(x_38);
lean_inc(x_1);
x_41 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_initializeWorker___lambda__1), 5, 3);
lean_closure_set(x_41, 0, x_1);
lean_closure_set(x_41, 1, x_38);
lean_closure_set(x_41, 2, x_40);
x_42 = l_Task_Priority_default;
x_43 = lean_io_map_task(x_41, x_36, x_42, x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_38);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_35);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set(x_50, 3, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
return x_9;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_9, 0);
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_9);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 2);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 2, x_10);
x_11 = lean_st_ref_set(x_3, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_22 = lean_apply_1(x_1, x_20);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_21);
x_24 = lean_st_ref_set(x_3, x_23, x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updatePendingRequests___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_updatePendingRequests(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at_Lean_Server_FileWorker_updateDocument___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Server_FileWorker_updateDocument___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_FileWorker_updateDocument___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Server_Snapshots_instInhabitedSnapshot;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_11);
x_14 = lean_st_ref_set(x_5, x_8, x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = lean_st_ref_set(x_5, x_24, x_9);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__2(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_IO_sleep(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_CancelToken_check___at_Lean_Server_FileWorker_updateDocument___spec__1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = 2;
x_7 = lean_io_exit(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_updateDocument___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Server_Snapshots_Snapshot_endPos(x_2);
x_4 = lean_nat_dec_lt(x_3, x_1);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
x_8 = l_Lean_Lsp_InitializeParams_editDelay(x_7);
lean_dec(x_7);
x_9 = lean_uint32_of_nat(x_8);
lean_dec(x_8);
x_10 = l_IO_sleep(x_9, x_6);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_List_redLength___rarg(x_4);
x_13 = lean_mk_empty_array_with_capacity(x_12);
lean_dec(x_12);
x_14 = l_List_toArrayAux___rarg(x_4, x_13);
x_15 = l_Lean_Server_FileWorker_unfoldCmdSnaps(x_2, x_14, x_3, x_1, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.Option.BasicAux", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option.get!", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value is none", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__1;
x_2 = l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__2;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_MonadExcept_ofExcept___at_Lean_Server_FileWorker_updateDocument___spec__2(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_14, 2);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_String_firstDiffPos(x_16, x_18);
lean_dec(x_18);
x_20 = l_IO_AsyncList_getFinishedPrefix___rarg(x_3, x_13);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__4;
x_228 = l_panic___at_Lean_Server_FileWorker_updateDocument___spec__3(x_227);
x_21 = x_228;
goto block_226;
}
else
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_12, 0);
lean_inc(x_229);
lean_dec(x_12);
x_21 = x_229;
goto block_226;
}
block_226:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_21, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
lean_ctor_set(x_21, 2, x_5);
lean_ctor_set(x_21, 1, x_4);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_updateDocument___lambda__4___boxed), 2, 1);
lean_closure_set(x_28, 0, x_19);
x_29 = l_List_takeWhile___rarg(x_28, x_27);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_List_lengthTRAux___rarg(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_dec_le(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Lean_Server_Snapshots_instInhabitedSnapshot;
lean_inc(x_29);
x_35 = l_List_getLast_x21___rarg(x_34, x_29);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_nat_dec_le(x_36, x_31);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_31);
x_38 = l_Lean_Server_Snapshots_parseNextCmd(x_8, x_21, x_23);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = l_Lean_Syntax_structEq(x_39, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = l_List_dropLast___rarg(x_29);
x_44 = lean_box(0);
x_45 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_6, x_2, x_7, x_43, x_44, x_40);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_tag(x_45, 0);
lean_ctor_set(x_45, 0, x_55);
return x_45;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_45, 0);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_45);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_box(0);
x_61 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_6, x_2, x_7, x_29, x_60, x_40);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_61, 0);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set_tag(x_61, 0);
lean_ctor_set(x_61, 0, x_71);
return x_61;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_61, 0);
x_73 = lean_ctor_get(x_61, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_61);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_21);
x_76 = lean_nat_sub(x_31, x_36);
lean_dec(x_31);
x_77 = l_List_get_x21___rarg(x_34, x_29, x_76);
x_78 = l_Lean_Server_Snapshots_parseNextCmd(x_8, x_77, x_23);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_dec(x_35);
x_82 = l_Lean_Syntax_structEq(x_79, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = l_List_dropLast___rarg(x_29);
x_84 = lean_box(0);
x_85 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_6, x_2, x_7, x_83, x_84, x_80);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_85, 0);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_85);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_85);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_85, 0);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set_tag(x_85, 0);
lean_ctor_set(x_85, 0, x_95);
return x_85;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_85, 0);
x_97 = lean_ctor_get(x_85, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_85);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_box(0);
x_101 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_6, x_2, x_7, x_29, x_100, x_80);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_101, 0, x_104);
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_101);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_101, 0);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set_tag(x_101, 0);
lean_ctor_set(x_101, 0, x_111);
return x_101;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_101, 0);
x_113 = lean_ctor_get(x_101, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_101);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_8);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_21);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_box(0);
x_119 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_6, x_2, x_7, x_117, x_118, x_23);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_119, 0, x_122);
return x_119;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_119);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_123);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_119);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_119, 0);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set_tag(x_119, 0);
lean_ctor_set(x_119, 0, x_129);
return x_119;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_119, 0);
x_131 = lean_ctor_get(x_119, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_119);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_130);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_134 = lean_ctor_get(x_21, 0);
x_135 = lean_ctor_get(x_21, 3);
x_136 = lean_ctor_get(x_21, 4);
x_137 = lean_ctor_get(x_21, 5);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_21);
x_138 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_4);
lean_ctor_set(x_138, 2, x_5);
lean_ctor_set(x_138, 3, x_135);
lean_ctor_set(x_138, 4, x_136);
lean_ctor_set(x_138, 5, x_137);
x_139 = lean_ctor_get(x_22, 0);
lean_inc(x_139);
lean_dec(x_22);
x_140 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_updateDocument___lambda__4___boxed), 2, 1);
lean_closure_set(x_140, 0, x_19);
x_141 = l_List_takeWhile___rarg(x_140, x_139);
x_142 = lean_unsigned_to_nat(0u);
x_143 = l_List_lengthTRAux___rarg(x_141, x_142);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_dec_le(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = l_Lean_Server_Snapshots_instInhabitedSnapshot;
lean_inc(x_141);
x_147 = l_List_getLast_x21___rarg(x_146, x_141);
x_148 = lean_unsigned_to_nat(2u);
x_149 = lean_nat_dec_le(x_148, x_143);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec(x_143);
x_150 = l_Lean_Server_Snapshots_parseNextCmd(x_8, x_138, x_23);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_147, 1);
lean_inc(x_153);
lean_dec(x_147);
x_154 = l_Lean_Syntax_structEq(x_151, x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = l_List_dropLast___rarg(x_141);
x_156 = lean_box(0);
x_157 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_6, x_2, x_7, x_155, x_156, x_152);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_158);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_157, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_165 = x_157;
} else {
 lean_dec_ref(x_157);
 x_165 = lean_box(0);
}
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_163);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_165;
 lean_ctor_set_tag(x_167, 0);
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_164);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_box(0);
x_169 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_6, x_2, x_7, x_141, x_168, x_152);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_170);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_169, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_169, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_177 = x_169;
} else {
 lean_dec_ref(x_169);
 x_177 = lean_box(0);
}
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_175);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
 lean_ctor_set_tag(x_179, 0);
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
lean_dec(x_138);
x_180 = lean_nat_sub(x_143, x_148);
lean_dec(x_143);
x_181 = l_List_get_x21___rarg(x_146, x_141, x_180);
x_182 = l_Lean_Server_Snapshots_parseNextCmd(x_8, x_181, x_23);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_ctor_get(x_147, 1);
lean_inc(x_185);
lean_dec(x_147);
x_186 = l_Lean_Syntax_structEq(x_183, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = l_List_dropLast___rarg(x_141);
x_188 = lean_box(0);
x_189 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_6, x_2, x_7, x_187, x_188, x_184);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_190);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_191);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_189, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_189, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_197 = x_189;
} else {
 lean_dec_ref(x_189);
 x_197 = lean_box(0);
}
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_195);
if (lean_is_scalar(x_197)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_197;
 lean_ctor_set_tag(x_199, 0);
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_196);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_box(0);
x_201 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_6, x_2, x_7, x_141, x_200, x_184);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_204 = x_201;
} else {
 lean_dec_ref(x_201);
 x_204 = lean_box(0);
}
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_202);
if (lean_is_scalar(x_204)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_204;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_201, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_209 = x_201;
} else {
 lean_dec_ref(x_201);
 x_209 = lean_box(0);
}
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_207);
if (lean_is_scalar(x_209)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_209;
 lean_ctor_set_tag(x_211, 0);
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_208);
return x_211;
}
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_8);
x_212 = lean_box(0);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_138);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_box(0);
x_215 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_6, x_2, x_7, x_213, x_214, x_23);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_218 = x_215;
} else {
 lean_dec_ref(x_215);
 x_218 = lean_box(0);
}
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_216);
if (lean_is_scalar(x_218)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_218;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_217);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_215, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_215, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_223 = x_215;
} else {
 lean_dec_ref(x_215);
 x_223 = lean_box(0);
}
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_221);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
 lean_ctor_set_tag(x_225, 0);
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
return x_225;
}
}
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_230 = !lean_is_exclusive(x_11);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_11, 0);
x_232 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_232);
return x_11;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_11, 0);
x_234 = lean_ctor_get(x_11, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_11);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_233);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_updateDocument___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_AsyncList_waitHead_x3f___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
x_10 = l_Lean_Server_FileWorker_CancelToken_set(x_9, x_7);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = l_Lean_Server_DocumentMeta_mkInputContext(x_1);
lean_inc(x_16);
x_17 = l_Lean_Parser_parseHeader(x_16, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_Server_FileWorker_CancelToken_new(x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
x_27 = l_Lean_Server_FileWorker_updateDocument___closed__1;
lean_inc(x_26);
x_28 = l_IO_AsyncList_waitFind_x3f___rarg(x_27, x_26);
lean_inc(x_21);
x_29 = l_Lean_Syntax_structEq(x_15, x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint32_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
x_30 = lean_ctor_get(x_2, 4);
lean_inc(x_30);
x_31 = l_Lean_Lsp_InitializeParams_editDelay(x_30);
lean_dec(x_30);
x_32 = lean_uint32_of_nat(x_31);
lean_dec(x_31);
x_33 = lean_box_uint32(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_updateDocument___lambda__2___boxed), 2, 1);
lean_closure_set(x_34, 0, x_33);
lean_inc(x_24);
x_35 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_updateDocument___lambda__3___boxed), 3, 1);
lean_closure_set(x_35, 0, x_24);
x_36 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
x_37 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Task_Priority_dedicated;
x_39 = lean_io_as_task(x_37, x_38, x_25);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Server_FileWorker_updateDocument___lambda__1(x_1, x_24, x_40, x_2, x_3, x_41);
lean_dec(x_3);
lean_dec(x_2);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_24);
lean_inc(x_2);
lean_inc(x_1);
x_43 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_updateDocument___lambda__6___boxed), 10, 8);
lean_closure_set(x_43, 0, x_8);
lean_closure_set(x_43, 1, x_1);
lean_closure_set(x_43, 2, x_26);
lean_closure_set(x_43, 3, x_21);
lean_closure_set(x_43, 4, x_22);
lean_closure_set(x_43, 5, x_2);
lean_closure_set(x_43, 6, x_24);
lean_closure_set(x_43, 7, x_16);
x_44 = l_Task_Priority_dedicated;
x_45 = lean_io_map_task(x_43, x_28, x_44, x_25);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Server_FileWorker_updateDocument___lambda__1(x_1, x_24, x_46, x_2, x_3, x_47);
lean_dec(x_3);
lean_dec(x_2);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_CancelToken_check___at_Lean_Server_FileWorker_updateDocument___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_CancelToken_check___at_Lean_Server_FileWorker_updateDocument___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Server_FileWorker_updateDocument___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at_Lean_Server_FileWorker_updateDocument___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_updateDocument___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Lean_Server_FileWorker_updateDocument___lambda__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_updateDocument___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_FileWorker_updateDocument___lambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_updateDocument___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_updateDocument___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Server_FileWorker_updateDocument___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleDidChange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected version number", 23);
return x_1;
}
}
static uint8_t _init_l_Lean_Server_FileWorker_handleDidChange___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Server_FileWorker_handleDidChange___closed__3() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleDidChange___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Got outdated version number: ", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleDidChange___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ≤ ", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleDidChange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_st_ref_get(x_3, x_4);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_handleDidChange___closed__1;
x_11 = l_IO_throwServerError___rarg(x_10, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_nat_dec_le(x_16, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_19);
x_21 = l_Array_isEmpty___rarg(x_6);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Server_FileWorker_handleDidChange___closed__2;
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_7);
x_24 = lean_ctor_get(x_18, 2);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_Server_foldDocumentChanges(x_6, x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Lean_Server_FileWorker_updateDocument(x_26, x_2, x_3, x_14);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Server_FileWorker_handleDidChange___closed__3;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
lean_ctor_set(x_7, 0, x_29);
return x_7;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_7);
x_30 = lean_ctor_get(x_18, 2);
lean_inc(x_30);
lean_dec(x_18);
x_31 = l_Lean_Server_foldDocumentChanges(x_6, x_30);
lean_dec(x_6);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_16);
lean_ctor_set(x_32, 2, x_31);
x_33 = l_Lean_Server_FileWorker_updateDocument(x_32, x_2, x_3, x_14);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_18);
lean_dec(x_15);
lean_free_object(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_34 = l_Nat_repr(x_16);
x_35 = l_Lean_Server_FileWorker_handleDidChange___closed__4;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_Server_FileWorker_handleDidChange___closed__5;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_Nat_repr(x_19);
x_40 = lean_string_append(x_38, x_39);
lean_dec(x_39);
x_41 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_42, x_14);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
x_46 = lean_ctor_get(x_5, 0);
lean_inc(x_46);
lean_dec(x_5);
x_47 = lean_ctor_get(x_8, 0);
lean_inc(x_47);
lean_dec(x_8);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
x_51 = lean_nat_dec_le(x_47, x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_50);
x_52 = l_Array_isEmpty___rarg(x_6);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Server_FileWorker_handleDidChange___closed__2;
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_49, 2);
lean_inc(x_56);
lean_dec(x_49);
x_57 = l_Lean_Server_foldDocumentChanges(x_6, x_56);
lean_dec(x_6);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_46);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 2, x_57);
x_59 = l_Lean_Server_FileWorker_updateDocument(x_58, x_2, x_3, x_45);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = l_Lean_Server_FileWorker_handleDidChange___closed__3;
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_45);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_49, 2);
lean_inc(x_63);
lean_dec(x_49);
x_64 = l_Lean_Server_foldDocumentChanges(x_6, x_63);
lean_dec(x_6);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_47);
lean_ctor_set(x_65, 2, x_64);
x_66 = l_Lean_Server_FileWorker_updateDocument(x_65, x_2, x_3, x_45);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_67 = l_Nat_repr(x_47);
x_68 = l_Lean_Server_FileWorker_handleDidChange___closed__4;
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
x_70 = l_Lean_Server_FileWorker_handleDidChange___closed__5;
x_71 = lean_string_append(x_69, x_70);
x_72 = l_Nat_repr(x_50);
x_73 = lean_string_append(x_71, x_72);
lean_dec(x_72);
x_74 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_75 = lean_string_append(x_73, x_74);
x_76 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_75, x_45);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_inc(x_1);
x_9 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151_(x_1, x_6);
switch (x_9) {
case 0:
{
uint8_t x_10; 
x_10 = l_Lean_RBNode_isBlack___rarg(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_5);
x_12 = 0;
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_5);
x_14 = l_Lean_RBNode_balLeft___rarg(x_13, x_6, x_7, x_8);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = l_Lean_RBNode_appendTrees___rarg(x_5, x_8);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___rarg(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_8);
x_18 = 0;
lean_ctor_set(x_2, 3, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_8);
x_20 = l_Lean_RBNode_balRight___rarg(x_5, x_6, x_7, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_22);
lean_inc(x_1);
x_25 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151_(x_1, x_22);
switch (x_25) {
case 0:
{
uint8_t x_26; 
x_26 = l_Lean_RBNode_isBlack___rarg(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_21);
x_31 = l_Lean_RBNode_balLeft___rarg(x_30, x_22, x_23, x_24);
return x_31;
}
}
case 1:
{
lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_32 = l_Lean_RBNode_appendTrees___rarg(x_21, x_24);
return x_32;
}
default: 
{
uint8_t x_33; 
x_33 = l_Lean_RBNode_isBlack___rarg(x_24);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_24);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_24);
x_38 = l_Lean_RBNode_balRight___rarg(x_21, x_22, x_23, x_37);
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Server_FileWorker_handleCancelRequest___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_handleCancelRequest___spec__2(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_RBNode_erase___at_Lean_Server_FileWorker_handleCancelRequest___spec__1), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Server_FileWorker_updatePendingRequests(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleCancelRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleCancelRequest(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_10 = l_Lean_Server_rpcReleaseRef(x_9, x_5);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_box(0);
x_3 = x_13;
x_4 = x_14;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_11 = l_Lean_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_free_object(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_mono_ms_now(x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = lean_st_ref_take(x_13, x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1(x_17, x_19, x_20, x_25, x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
x_29 = lean_nat_add(x_15, x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_st_ref_set(x_13, x_30, x_23);
lean_dec(x_13);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_5);
x_38 = lean_ctor_get(x_36, 3);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_40 = l_Lean_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1(x_38, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_io_mono_ms_now(x_37);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_1, 1);
x_48 = lean_array_get_size(x_47);
x_49 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_50 = 0;
x_51 = lean_st_ref_take(x_43, x_46);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_box(0);
x_56 = l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1(x_47, x_49, x_50, x_55, x_54);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
x_59 = lean_nat_add(x_45, x_58);
lean_dec(x_45);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_st_ref_set(x_43, x_60, x_53);
lean_dec(x_43);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Server_FileWorker_handleRpcRelease___spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcRelease___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleRpcRelease(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_11 = l_Lean_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_mono_ms_now(x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_13, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_15, x_18);
lean_dec(x_15);
x_21 = lean_st_ref_set(x_13, x_20, x_19);
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = lean_ctor_get(x_26, 3);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_30 = l_Lean_RBNode_find___at_Lean_Server_wrapRpcProcedure___elambda__1___spec__1(x_28, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_io_mono_ms_now(x_27);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_take(x_33, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Server_FileWorker_RpcSession_keptAlive(x_35, x_38);
lean_dec(x_35);
x_41 = lean_st_ref_set(x_33, x_40, x_39);
lean_dec(x_33);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcKeepAlive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_handleRpcKeepAlive(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_box_uint64(x_2);
x_7 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_unbox_uint64(x_11);
x_15 = lean_uint64_dec_lt(x_2, x_14);
if (x_15 == 0)
{
uint64_t x_16; uint8_t x_17; 
x_16 = lean_unbox_uint64(x_11);
x_17 = lean_uint64_dec_eq(x_2, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_13, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 3, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
else
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_11);
x_20 = 0;
x_21 = lean_box_uint64(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_20);
return x_1;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_10, x_2, x_3);
x_23 = 0;
lean_ctor_set(x_1, 0, x_22);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_23);
return x_1;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_28 = lean_unbox_uint64(x_25);
x_29 = lean_uint64_dec_lt(x_2, x_28);
if (x_29 == 0)
{
uint64_t x_30; uint8_t x_31; 
x_30 = lean_unbox_uint64(x_25);
x_31 = lean_uint64_dec_eq(x_2, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_27, x_2, x_3);
x_33 = 0;
x_34 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_33);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_26);
lean_dec(x_25);
x_35 = 0;
x_36 = lean_box_uint64(x_2);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_3);
lean_ctor_set(x_37, 3, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_35);
return x_37;
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_24, x_2, x_3);
x_39 = 0;
x_40 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_25);
lean_ctor_set(x_40, 2, x_26);
lean_ctor_set(x_40, 3, x_27);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_1, 2);
x_45 = lean_ctor_get(x_1, 3);
x_46 = lean_unbox_uint64(x_43);
x_47 = lean_uint64_dec_lt(x_2, x_46);
if (x_47 == 0)
{
uint64_t x_48; uint8_t x_49; 
x_48 = lean_unbox_uint64(x_43);
x_49 = lean_uint64_dec_eq(x_2, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_45, x_2, x_3);
x_51 = lean_ctor_get_uint8(x_50, sizeof(void*)*4);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 3);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_50, 3);
lean_dec(x_55);
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
lean_ctor_set(x_50, 0, x_53);
x_57 = 1;
lean_ctor_set(x_1, 3, x_50);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_57);
return x_1;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_50, 1);
x_59 = lean_ctor_get(x_50, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_53);
lean_ctor_set_uint8(x_60, sizeof(void*)*4, x_51);
x_61 = 1;
lean_ctor_set(x_1, 3, x_60);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_61);
return x_1;
}
}
else
{
uint8_t x_62; 
x_62 = lean_ctor_get_uint8(x_53, sizeof(void*)*4);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_50);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_50, 1);
x_65 = lean_ctor_get(x_50, 2);
x_66 = lean_ctor_get(x_50, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_50, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_53);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_53, 0);
x_70 = lean_ctor_get(x_53, 1);
x_71 = lean_ctor_get(x_53, 2);
x_72 = lean_ctor_get(x_53, 3);
x_73 = 1;
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 2, x_44);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_73);
lean_ctor_set(x_50, 3, x_72);
lean_ctor_set(x_50, 2, x_71);
lean_ctor_set(x_50, 1, x_70);
lean_ctor_set(x_50, 0, x_69);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_73);
x_74 = 0;
lean_ctor_set(x_1, 3, x_50);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_74);
return x_1;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; uint8_t x_81; 
x_75 = lean_ctor_get(x_53, 0);
x_76 = lean_ctor_get(x_53, 1);
x_77 = lean_ctor_get(x_53, 2);
x_78 = lean_ctor_get(x_53, 3);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_53);
x_79 = 1;
x_80 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_80, 0, x_42);
lean_ctor_set(x_80, 1, x_43);
lean_ctor_set(x_80, 2, x_44);
lean_ctor_set(x_80, 3, x_52);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_79);
lean_ctor_set(x_50, 3, x_78);
lean_ctor_set(x_50, 2, x_77);
lean_ctor_set(x_50, 1, x_76);
lean_ctor_set(x_50, 0, x_75);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_79);
x_81 = 0;
lean_ctor_set(x_1, 3, x_50);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_80);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_81);
return x_1;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_82 = lean_ctor_get(x_50, 1);
x_83 = lean_ctor_get(x_50, 2);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_50);
x_84 = lean_ctor_get(x_53, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_53, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_53, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_53, 3);
lean_inc(x_87);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 x_88 = x_53;
} else {
 lean_dec_ref(x_53);
 x_88 = lean_box(0);
}
x_89 = 1;
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 4, 1);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_42);
lean_ctor_set(x_90, 1, x_43);
lean_ctor_set(x_90, 2, x_44);
lean_ctor_set(x_90, 3, x_52);
lean_ctor_set_uint8(x_90, sizeof(void*)*4, x_89);
x_91 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_85);
lean_ctor_set(x_91, 2, x_86);
lean_ctor_set(x_91, 3, x_87);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_89);
x_92 = 0;
lean_ctor_set(x_1, 3, x_91);
lean_ctor_set(x_1, 2, x_83);
lean_ctor_set(x_1, 1, x_82);
lean_ctor_set(x_1, 0, x_90);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
}
else
{
uint8_t x_93; 
lean_free_object(x_1);
x_93 = !lean_is_exclusive(x_53);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_53, 3);
lean_dec(x_94);
x_95 = lean_ctor_get(x_53, 2);
lean_dec(x_95);
x_96 = lean_ctor_get(x_53, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_53, 0);
lean_dec(x_97);
x_98 = 1;
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 2, x_44);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_98);
return x_53;
}
else
{
uint8_t x_99; lean_object* x_100; 
lean_dec(x_53);
x_99 = 1;
x_100 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_100, 0, x_42);
lean_ctor_set(x_100, 1, x_43);
lean_ctor_set(x_100, 2, x_44);
lean_ctor_set(x_100, 3, x_50);
lean_ctor_set_uint8(x_100, sizeof(void*)*4, x_99);
return x_100;
}
}
}
}
else
{
uint8_t x_101; 
x_101 = lean_ctor_get_uint8(x_52, sizeof(void*)*4);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_50);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_50, 0);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_52);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; 
x_105 = lean_ctor_get(x_52, 0);
x_106 = lean_ctor_get(x_52, 1);
x_107 = lean_ctor_get(x_52, 2);
x_108 = lean_ctor_get(x_52, 3);
x_109 = 1;
lean_ctor_set(x_52, 3, x_105);
lean_ctor_set(x_52, 2, x_44);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_109);
lean_ctor_set(x_50, 0, x_108);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_109);
x_110 = 0;
lean_ctor_set(x_1, 3, x_50);
lean_ctor_set(x_1, 2, x_107);
lean_ctor_set(x_1, 1, x_106);
lean_ctor_set(x_1, 0, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_110);
return x_1;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; uint8_t x_117; 
x_111 = lean_ctor_get(x_52, 0);
x_112 = lean_ctor_get(x_52, 1);
x_113 = lean_ctor_get(x_52, 2);
x_114 = lean_ctor_get(x_52, 3);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_52);
x_115 = 1;
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_42);
lean_ctor_set(x_116, 1, x_43);
lean_ctor_set(x_116, 2, x_44);
lean_ctor_set(x_116, 3, x_111);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_115);
lean_ctor_set(x_50, 0, x_114);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_115);
x_117 = 0;
lean_ctor_set(x_1, 3, x_50);
lean_ctor_set(x_1, 2, x_113);
lean_ctor_set(x_1, 1, x_112);
lean_ctor_set(x_1, 0, x_116);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_117);
return x_1;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_118 = lean_ctor_get(x_50, 1);
x_119 = lean_ctor_get(x_50, 2);
x_120 = lean_ctor_get(x_50, 3);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_50);
x_121 = lean_ctor_get(x_52, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_52, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_52, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_52, 3);
lean_inc(x_124);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 x_125 = x_52;
} else {
 lean_dec_ref(x_52);
 x_125 = lean_box(0);
}
x_126 = 1;
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(1, 4, 1);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_42);
lean_ctor_set(x_127, 1, x_43);
lean_ctor_set(x_127, 2, x_44);
lean_ctor_set(x_127, 3, x_121);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_126);
x_128 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_118);
lean_ctor_set(x_128, 2, x_119);
lean_ctor_set(x_128, 3, x_120);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_126);
x_129 = 0;
lean_ctor_set(x_1, 3, x_128);
lean_ctor_set(x_1, 2, x_123);
lean_ctor_set(x_1, 1, x_122);
lean_ctor_set(x_1, 0, x_127);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_129);
return x_1;
}
}
else
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_50, 3);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_52);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_52, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_52, 2);
lean_dec(x_133);
x_134 = lean_ctor_get(x_52, 1);
lean_dec(x_134);
x_135 = lean_ctor_get(x_52, 0);
lean_dec(x_135);
x_136 = 1;
lean_ctor_set(x_52, 3, x_50);
lean_ctor_set(x_52, 2, x_44);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_136);
return x_52;
}
else
{
uint8_t x_137; lean_object* x_138; 
lean_dec(x_52);
x_137 = 1;
x_138 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_138, 0, x_42);
lean_ctor_set(x_138, 1, x_43);
lean_ctor_set(x_138, 2, x_44);
lean_ctor_set(x_138, 3, x_50);
lean_ctor_set_uint8(x_138, sizeof(void*)*4, x_137);
return x_138;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_130, sizeof(void*)*4);
if (x_139 == 0)
{
uint8_t x_140; 
lean_free_object(x_1);
x_140 = !lean_is_exclusive(x_50);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_50, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_50, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_130);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_130, 0);
x_145 = lean_ctor_get(x_130, 1);
x_146 = lean_ctor_get(x_130, 2);
x_147 = lean_ctor_get(x_130, 3);
x_148 = 1;
lean_inc(x_52);
lean_ctor_set(x_130, 3, x_52);
lean_ctor_set(x_130, 2, x_44);
lean_ctor_set(x_130, 1, x_43);
lean_ctor_set(x_130, 0, x_42);
x_149 = !lean_is_exclusive(x_52);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_52, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_52, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_52, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_52, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_148);
lean_ctor_set(x_52, 3, x_147);
lean_ctor_set(x_52, 2, x_146);
lean_ctor_set(x_52, 1, x_145);
lean_ctor_set(x_52, 0, x_144);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_148);
x_154 = 0;
lean_ctor_set(x_50, 3, x_52);
lean_ctor_set(x_50, 0, x_130);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_154);
return x_50;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_52);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_148);
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_145);
lean_ctor_set(x_155, 2, x_146);
lean_ctor_set(x_155, 3, x_147);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_148);
x_156 = 0;
lean_ctor_set(x_50, 3, x_155);
lean_ctor_set(x_50, 0, x_130);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_156);
return x_50;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_157 = lean_ctor_get(x_130, 0);
x_158 = lean_ctor_get(x_130, 1);
x_159 = lean_ctor_get(x_130, 2);
x_160 = lean_ctor_get(x_130, 3);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_130);
x_161 = 1;
lean_inc(x_52);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_42);
lean_ctor_set(x_162, 1, x_43);
lean_ctor_set(x_162, 2, x_44);
lean_ctor_set(x_162, 3, x_52);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 x_163 = x_52;
} else {
 lean_dec_ref(x_52);
 x_163 = lean_box(0);
}
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_161);
x_165 = 0;
lean_ctor_set(x_50, 3, x_164);
lean_ctor_set(x_50, 0, x_162);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_165);
return x_50;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_50, 1);
x_167 = lean_ctor_get(x_50, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_50);
x_168 = lean_ctor_get(x_130, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_130, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_130, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_130, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 x_172 = x_130;
} else {
 lean_dec_ref(x_130);
 x_172 = lean_box(0);
}
x_173 = 1;
lean_inc(x_52);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_42);
lean_ctor_set(x_174, 1, x_43);
lean_ctor_set(x_174, 2, x_44);
lean_ctor_set(x_174, 3, x_52);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 x_175 = x_52;
} else {
 lean_dec_ref(x_52);
 x_175 = lean_box(0);
}
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_173);
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_173);
x_177 = 0;
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_166);
lean_ctor_set(x_178, 2, x_167);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_50);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_50, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_50, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_52);
if (x_182 == 0)
{
uint8_t x_183; 
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_139);
x_183 = 1;
lean_ctor_set(x_1, 3, x_50);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_184 = lean_ctor_get(x_52, 0);
x_185 = lean_ctor_get(x_52, 1);
x_186 = lean_ctor_get(x_52, 2);
x_187 = lean_ctor_get(x_52, 3);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_52);
x_188 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_186);
lean_ctor_set(x_188, 3, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_139);
lean_ctor_set(x_50, 0, x_188);
x_189 = 1;
lean_ctor_set(x_1, 3, x_50);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_190 = lean_ctor_get(x_50, 1);
x_191 = lean_ctor_get(x_50, 2);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_50);
x_192 = lean_ctor_get(x_52, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_52, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_52, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_52, 3);
lean_inc(x_195);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 x_196 = x_52;
} else {
 lean_dec_ref(x_52);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 4, 1);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_193);
lean_ctor_set(x_197, 2, x_194);
lean_ctor_set(x_197, 3, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_139);
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_190);
lean_ctor_set(x_198, 2, x_191);
lean_ctor_set(x_198, 3, x_130);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_51);
x_199 = 1;
lean_ctor_set(x_1, 3, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_200; 
x_200 = 1;
lean_ctor_set(x_1, 3, x_50);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
else
{
uint8_t x_201; lean_object* x_202; 
lean_dec(x_44);
lean_dec(x_43);
x_201 = 1;
x_202 = lean_box_uint64(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_202);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_201);
return x_1;
}
}
else
{
lean_object* x_203; uint8_t x_204; 
x_203 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_42, x_2, x_3);
x_204 = lean_ctor_get_uint8(x_203, sizeof(void*)*4);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_203, 3);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_203);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_203, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_203, 0);
lean_dec(x_209);
lean_ctor_set(x_203, 0, x_206);
x_210 = 1;
lean_ctor_set(x_1, 0, x_203);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_211 = lean_ctor_get(x_203, 1);
x_212 = lean_ctor_get(x_203, 2);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_203);
x_213 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_213, 0, x_206);
lean_ctor_set(x_213, 1, x_211);
lean_ctor_set(x_213, 2, x_212);
lean_ctor_set(x_213, 3, x_206);
lean_ctor_set_uint8(x_213, sizeof(void*)*4, x_204);
x_214 = 1;
lean_ctor_set(x_1, 0, x_213);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_214);
return x_1;
}
}
else
{
uint8_t x_215; 
x_215 = lean_ctor_get_uint8(x_206, sizeof(void*)*4);
if (x_215 == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_203);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_203, 1);
x_218 = lean_ctor_get(x_203, 2);
x_219 = lean_ctor_get(x_203, 3);
lean_dec(x_219);
x_220 = lean_ctor_get(x_203, 0);
lean_dec(x_220);
x_221 = !lean_is_exclusive(x_206);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; uint8_t x_227; 
x_222 = lean_ctor_get(x_206, 0);
x_223 = lean_ctor_get(x_206, 1);
x_224 = lean_ctor_get(x_206, 2);
x_225 = lean_ctor_get(x_206, 3);
x_226 = 1;
lean_ctor_set(x_206, 3, x_222);
lean_ctor_set(x_206, 2, x_218);
lean_ctor_set(x_206, 1, x_217);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_226);
lean_ctor_set(x_203, 3, x_45);
lean_ctor_set(x_203, 2, x_44);
lean_ctor_set(x_203, 1, x_43);
lean_ctor_set(x_203, 0, x_225);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_226);
x_227 = 0;
lean_ctor_set(x_1, 3, x_203);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_227);
return x_1;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; uint8_t x_234; 
x_228 = lean_ctor_get(x_206, 0);
x_229 = lean_ctor_get(x_206, 1);
x_230 = lean_ctor_get(x_206, 2);
x_231 = lean_ctor_get(x_206, 3);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_206);
x_232 = 1;
x_233 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_233, 0, x_205);
lean_ctor_set(x_233, 1, x_217);
lean_ctor_set(x_233, 2, x_218);
lean_ctor_set(x_233, 3, x_228);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_232);
lean_ctor_set(x_203, 3, x_45);
lean_ctor_set(x_203, 2, x_44);
lean_ctor_set(x_203, 1, x_43);
lean_ctor_set(x_203, 0, x_231);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_232);
x_234 = 0;
lean_ctor_set(x_1, 3, x_203);
lean_ctor_set(x_1, 2, x_230);
lean_ctor_set(x_1, 1, x_229);
lean_ctor_set(x_1, 0, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_234);
return x_1;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_235 = lean_ctor_get(x_203, 1);
x_236 = lean_ctor_get(x_203, 2);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_203);
x_237 = lean_ctor_get(x_206, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_206, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_206, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_206, 3);
lean_inc(x_240);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_241 = x_206;
} else {
 lean_dec_ref(x_206);
 x_241 = lean_box(0);
}
x_242 = 1;
if (lean_is_scalar(x_241)) {
 x_243 = lean_alloc_ctor(1, 4, 1);
} else {
 x_243 = x_241;
}
lean_ctor_set(x_243, 0, x_205);
lean_ctor_set(x_243, 1, x_235);
lean_ctor_set(x_243, 2, x_236);
lean_ctor_set(x_243, 3, x_237);
lean_ctor_set_uint8(x_243, sizeof(void*)*4, x_242);
x_244 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_244, 0, x_240);
lean_ctor_set(x_244, 1, x_43);
lean_ctor_set(x_244, 2, x_44);
lean_ctor_set(x_244, 3, x_45);
lean_ctor_set_uint8(x_244, sizeof(void*)*4, x_242);
x_245 = 0;
lean_ctor_set(x_1, 3, x_244);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_238);
lean_ctor_set(x_1, 0, x_243);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_245);
return x_1;
}
}
else
{
uint8_t x_246; 
lean_free_object(x_1);
x_246 = !lean_is_exclusive(x_206);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_247 = lean_ctor_get(x_206, 3);
lean_dec(x_247);
x_248 = lean_ctor_get(x_206, 2);
lean_dec(x_248);
x_249 = lean_ctor_get(x_206, 1);
lean_dec(x_249);
x_250 = lean_ctor_get(x_206, 0);
lean_dec(x_250);
x_251 = 1;
lean_ctor_set(x_206, 3, x_45);
lean_ctor_set(x_206, 2, x_44);
lean_ctor_set(x_206, 1, x_43);
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_251);
return x_206;
}
else
{
uint8_t x_252; lean_object* x_253; 
lean_dec(x_206);
x_252 = 1;
x_253 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_253, 0, x_203);
lean_ctor_set(x_253, 1, x_43);
lean_ctor_set(x_253, 2, x_44);
lean_ctor_set(x_253, 3, x_45);
lean_ctor_set_uint8(x_253, sizeof(void*)*4, x_252);
return x_253;
}
}
}
}
else
{
uint8_t x_254; 
x_254 = lean_ctor_get_uint8(x_205, sizeof(void*)*4);
if (x_254 == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_203);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_256 = lean_ctor_get(x_203, 1);
x_257 = lean_ctor_get(x_203, 2);
x_258 = lean_ctor_get(x_203, 3);
x_259 = lean_ctor_get(x_203, 0);
lean_dec(x_259);
x_260 = !lean_is_exclusive(x_205);
if (x_260 == 0)
{
uint8_t x_261; uint8_t x_262; 
x_261 = 1;
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_261);
lean_ctor_set(x_203, 3, x_45);
lean_ctor_set(x_203, 2, x_44);
lean_ctor_set(x_203, 1, x_43);
lean_ctor_set(x_203, 0, x_258);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_261);
x_262 = 0;
lean_ctor_set(x_1, 3, x_203);
lean_ctor_set(x_1, 2, x_257);
lean_ctor_set(x_1, 1, x_256);
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_262);
return x_1;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; uint8_t x_269; 
x_263 = lean_ctor_get(x_205, 0);
x_264 = lean_ctor_get(x_205, 1);
x_265 = lean_ctor_get(x_205, 2);
x_266 = lean_ctor_get(x_205, 3);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_205);
x_267 = 1;
x_268 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_268, 0, x_263);
lean_ctor_set(x_268, 1, x_264);
lean_ctor_set(x_268, 2, x_265);
lean_ctor_set(x_268, 3, x_266);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
lean_ctor_set(x_203, 3, x_45);
lean_ctor_set(x_203, 2, x_44);
lean_ctor_set(x_203, 1, x_43);
lean_ctor_set(x_203, 0, x_258);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_267);
x_269 = 0;
lean_ctor_set(x_1, 3, x_203);
lean_ctor_set(x_1, 2, x_257);
lean_ctor_set(x_1, 1, x_256);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
return x_1;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_270 = lean_ctor_get(x_203, 1);
x_271 = lean_ctor_get(x_203, 2);
x_272 = lean_ctor_get(x_203, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_203);
x_273 = lean_ctor_get(x_205, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_205, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_205, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_205, 3);
lean_inc(x_276);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_277 = x_205;
} else {
 lean_dec_ref(x_205);
 x_277 = lean_box(0);
}
x_278 = 1;
if (lean_is_scalar(x_277)) {
 x_279 = lean_alloc_ctor(1, 4, 1);
} else {
 x_279 = x_277;
}
lean_ctor_set(x_279, 0, x_273);
lean_ctor_set(x_279, 1, x_274);
lean_ctor_set(x_279, 2, x_275);
lean_ctor_set(x_279, 3, x_276);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_272);
lean_ctor_set(x_280, 1, x_43);
lean_ctor_set(x_280, 2, x_44);
lean_ctor_set(x_280, 3, x_45);
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_278);
x_281 = 0;
lean_ctor_set(x_1, 3, x_280);
lean_ctor_set(x_1, 2, x_271);
lean_ctor_set(x_1, 1, x_270);
lean_ctor_set(x_1, 0, x_279);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_281);
return x_1;
}
}
else
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_203, 3);
lean_inc(x_282);
if (lean_obj_tag(x_282) == 0)
{
uint8_t x_283; 
lean_free_object(x_1);
x_283 = !lean_is_exclusive(x_205);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_284 = lean_ctor_get(x_205, 3);
lean_dec(x_284);
x_285 = lean_ctor_get(x_205, 2);
lean_dec(x_285);
x_286 = lean_ctor_get(x_205, 1);
lean_dec(x_286);
x_287 = lean_ctor_get(x_205, 0);
lean_dec(x_287);
x_288 = 1;
lean_ctor_set(x_205, 3, x_45);
lean_ctor_set(x_205, 2, x_44);
lean_ctor_set(x_205, 1, x_43);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_288);
return x_205;
}
else
{
uint8_t x_289; lean_object* x_290; 
lean_dec(x_205);
x_289 = 1;
x_290 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_290, 0, x_203);
lean_ctor_set(x_290, 1, x_43);
lean_ctor_set(x_290, 2, x_44);
lean_ctor_set(x_290, 3, x_45);
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_289);
return x_290;
}
}
else
{
uint8_t x_291; 
x_291 = lean_ctor_get_uint8(x_282, sizeof(void*)*4);
if (x_291 == 0)
{
uint8_t x_292; 
lean_free_object(x_1);
x_292 = !lean_is_exclusive(x_203);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_203, 1);
x_294 = lean_ctor_get(x_203, 2);
x_295 = lean_ctor_get(x_203, 3);
lean_dec(x_295);
x_296 = lean_ctor_get(x_203, 0);
lean_dec(x_296);
x_297 = !lean_is_exclusive(x_282);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_303; 
x_298 = lean_ctor_get(x_282, 0);
x_299 = lean_ctor_get(x_282, 1);
x_300 = lean_ctor_get(x_282, 2);
x_301 = lean_ctor_get(x_282, 3);
x_302 = 1;
lean_inc(x_205);
lean_ctor_set(x_282, 3, x_298);
lean_ctor_set(x_282, 2, x_294);
lean_ctor_set(x_282, 1, x_293);
lean_ctor_set(x_282, 0, x_205);
x_303 = !lean_is_exclusive(x_205);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_304 = lean_ctor_get(x_205, 3);
lean_dec(x_304);
x_305 = lean_ctor_get(x_205, 2);
lean_dec(x_305);
x_306 = lean_ctor_get(x_205, 1);
lean_dec(x_306);
x_307 = lean_ctor_get(x_205, 0);
lean_dec(x_307);
lean_ctor_set_uint8(x_282, sizeof(void*)*4, x_302);
lean_ctor_set(x_205, 3, x_45);
lean_ctor_set(x_205, 2, x_44);
lean_ctor_set(x_205, 1, x_43);
lean_ctor_set(x_205, 0, x_301);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_302);
x_308 = 0;
lean_ctor_set(x_203, 3, x_205);
lean_ctor_set(x_203, 2, x_300);
lean_ctor_set(x_203, 1, x_299);
lean_ctor_set(x_203, 0, x_282);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_308);
return x_203;
}
else
{
lean_object* x_309; uint8_t x_310; 
lean_dec(x_205);
lean_ctor_set_uint8(x_282, sizeof(void*)*4, x_302);
x_309 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_309, 0, x_301);
lean_ctor_set(x_309, 1, x_43);
lean_ctor_set(x_309, 2, x_44);
lean_ctor_set(x_309, 3, x_45);
lean_ctor_set_uint8(x_309, sizeof(void*)*4, x_302);
x_310 = 0;
lean_ctor_set(x_203, 3, x_309);
lean_ctor_set(x_203, 2, x_300);
lean_ctor_set(x_203, 1, x_299);
lean_ctor_set(x_203, 0, x_282);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_310);
return x_203;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_311 = lean_ctor_get(x_282, 0);
x_312 = lean_ctor_get(x_282, 1);
x_313 = lean_ctor_get(x_282, 2);
x_314 = lean_ctor_get(x_282, 3);
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_282);
x_315 = 1;
lean_inc(x_205);
x_316 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_316, 0, x_205);
lean_ctor_set(x_316, 1, x_293);
lean_ctor_set(x_316, 2, x_294);
lean_ctor_set(x_316, 3, x_311);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_317 = x_205;
} else {
 lean_dec_ref(x_205);
 x_317 = lean_box(0);
}
lean_ctor_set_uint8(x_316, sizeof(void*)*4, x_315);
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 4, 1);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_314);
lean_ctor_set(x_318, 1, x_43);
lean_ctor_set(x_318, 2, x_44);
lean_ctor_set(x_318, 3, x_45);
lean_ctor_set_uint8(x_318, sizeof(void*)*4, x_315);
x_319 = 0;
lean_ctor_set(x_203, 3, x_318);
lean_ctor_set(x_203, 2, x_313);
lean_ctor_set(x_203, 1, x_312);
lean_ctor_set(x_203, 0, x_316);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_319);
return x_203;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; 
x_320 = lean_ctor_get(x_203, 1);
x_321 = lean_ctor_get(x_203, 2);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_203);
x_322 = lean_ctor_get(x_282, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_282, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_282, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_282, 3);
lean_inc(x_325);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 lean_ctor_release(x_282, 2);
 lean_ctor_release(x_282, 3);
 x_326 = x_282;
} else {
 lean_dec_ref(x_282);
 x_326 = lean_box(0);
}
x_327 = 1;
lean_inc(x_205);
if (lean_is_scalar(x_326)) {
 x_328 = lean_alloc_ctor(1, 4, 1);
} else {
 x_328 = x_326;
}
lean_ctor_set(x_328, 0, x_205);
lean_ctor_set(x_328, 1, x_320);
lean_ctor_set(x_328, 2, x_321);
lean_ctor_set(x_328, 3, x_322);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_329 = x_205;
} else {
 lean_dec_ref(x_205);
 x_329 = lean_box(0);
}
lean_ctor_set_uint8(x_328, sizeof(void*)*4, x_327);
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 4, 1);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_325);
lean_ctor_set(x_330, 1, x_43);
lean_ctor_set(x_330, 2, x_44);
lean_ctor_set(x_330, 3, x_45);
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_327);
x_331 = 0;
x_332 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_332, 0, x_328);
lean_ctor_set(x_332, 1, x_323);
lean_ctor_set(x_332, 2, x_324);
lean_ctor_set(x_332, 3, x_330);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
return x_332;
}
}
else
{
uint8_t x_333; 
x_333 = !lean_is_exclusive(x_203);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_334 = lean_ctor_get(x_203, 3);
lean_dec(x_334);
x_335 = lean_ctor_get(x_203, 0);
lean_dec(x_335);
x_336 = !lean_is_exclusive(x_205);
if (x_336 == 0)
{
uint8_t x_337; 
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_291);
x_337 = 1;
lean_ctor_set(x_1, 0, x_203);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_337);
return x_1;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
x_338 = lean_ctor_get(x_205, 0);
x_339 = lean_ctor_get(x_205, 1);
x_340 = lean_ctor_get(x_205, 2);
x_341 = lean_ctor_get(x_205, 3);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_205);
x_342 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_342, 0, x_338);
lean_ctor_set(x_342, 1, x_339);
lean_ctor_set(x_342, 2, x_340);
lean_ctor_set(x_342, 3, x_341);
lean_ctor_set_uint8(x_342, sizeof(void*)*4, x_291);
lean_ctor_set(x_203, 0, x_342);
x_343 = 1;
lean_ctor_set(x_1, 0, x_203);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_344 = lean_ctor_get(x_203, 1);
x_345 = lean_ctor_get(x_203, 2);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_203);
x_346 = lean_ctor_get(x_205, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_205, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_205, 2);
lean_inc(x_348);
x_349 = lean_ctor_get(x_205, 3);
lean_inc(x_349);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 x_350 = x_205;
} else {
 lean_dec_ref(x_205);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 4, 1);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_346);
lean_ctor_set(x_351, 1, x_347);
lean_ctor_set(x_351, 2, x_348);
lean_ctor_set(x_351, 3, x_349);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_291);
x_352 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_344);
lean_ctor_set(x_352, 2, x_345);
lean_ctor_set(x_352, 3, x_282);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_204);
x_353 = 1;
lean_ctor_set(x_1, 0, x_352);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_354; 
x_354 = 1;
lean_ctor_set(x_1, 0, x_203);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_354);
return x_1;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint64_t x_359; uint8_t x_360; 
x_355 = lean_ctor_get(x_1, 0);
x_356 = lean_ctor_get(x_1, 1);
x_357 = lean_ctor_get(x_1, 2);
x_358 = lean_ctor_get(x_1, 3);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_1);
x_359 = lean_unbox_uint64(x_356);
x_360 = lean_uint64_dec_lt(x_2, x_359);
if (x_360 == 0)
{
uint64_t x_361; uint8_t x_362; 
x_361 = lean_unbox_uint64(x_356);
x_362 = lean_uint64_dec_eq(x_2, x_361);
if (x_362 == 0)
{
lean_object* x_363; uint8_t x_364; 
x_363 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_358, x_2, x_3);
x_364 = lean_ctor_get_uint8(x_363, sizeof(void*)*4);
if (x_364 == 0)
{
lean_object* x_365; 
x_365 = lean_ctor_get(x_363, 0);
lean_inc(x_365);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_363, 3);
lean_inc(x_366);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; 
x_367 = lean_ctor_get(x_363, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_363, 2);
lean_inc(x_368);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 lean_ctor_release(x_363, 2);
 lean_ctor_release(x_363, 3);
 x_369 = x_363;
} else {
 lean_dec_ref(x_363);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(1, 4, 1);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_366);
lean_ctor_set(x_370, 1, x_367);
lean_ctor_set(x_370, 2, x_368);
lean_ctor_set(x_370, 3, x_366);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_364);
x_371 = 1;
x_372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_372, 0, x_355);
lean_ctor_set(x_372, 1, x_356);
lean_ctor_set(x_372, 2, x_357);
lean_ctor_set(x_372, 3, x_370);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
return x_372;
}
else
{
uint8_t x_373; 
x_373 = lean_ctor_get_uint8(x_366, sizeof(void*)*4);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_374 = lean_ctor_get(x_363, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_363, 2);
lean_inc(x_375);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 lean_ctor_release(x_363, 2);
 lean_ctor_release(x_363, 3);
 x_376 = x_363;
} else {
 lean_dec_ref(x_363);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_366, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_366, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_366, 2);
lean_inc(x_379);
x_380 = lean_ctor_get(x_366, 3);
lean_inc(x_380);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 lean_ctor_release(x_366, 2);
 lean_ctor_release(x_366, 3);
 x_381 = x_366;
} else {
 lean_dec_ref(x_366);
 x_381 = lean_box(0);
}
x_382 = 1;
if (lean_is_scalar(x_381)) {
 x_383 = lean_alloc_ctor(1, 4, 1);
} else {
 x_383 = x_381;
}
lean_ctor_set(x_383, 0, x_355);
lean_ctor_set(x_383, 1, x_356);
lean_ctor_set(x_383, 2, x_357);
lean_ctor_set(x_383, 3, x_365);
lean_ctor_set_uint8(x_383, sizeof(void*)*4, x_382);
if (lean_is_scalar(x_376)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_376;
}
lean_ctor_set(x_384, 0, x_377);
lean_ctor_set(x_384, 1, x_378);
lean_ctor_set(x_384, 2, x_379);
lean_ctor_set(x_384, 3, x_380);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_382);
x_385 = 0;
x_386 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_374);
lean_ctor_set(x_386, 2, x_375);
lean_ctor_set(x_386, 3, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
return x_386;
}
else
{
lean_object* x_387; uint8_t x_388; lean_object* x_389; 
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 lean_ctor_release(x_366, 2);
 lean_ctor_release(x_366, 3);
 x_387 = x_366;
} else {
 lean_dec_ref(x_366);
 x_387 = lean_box(0);
}
x_388 = 1;
if (lean_is_scalar(x_387)) {
 x_389 = lean_alloc_ctor(1, 4, 1);
} else {
 x_389 = x_387;
}
lean_ctor_set(x_389, 0, x_355);
lean_ctor_set(x_389, 1, x_356);
lean_ctor_set(x_389, 2, x_357);
lean_ctor_set(x_389, 3, x_363);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
return x_389;
}
}
}
else
{
uint8_t x_390; 
x_390 = lean_ctor_get_uint8(x_365, sizeof(void*)*4);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; 
x_391 = lean_ctor_get(x_363, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_363, 2);
lean_inc(x_392);
x_393 = lean_ctor_get(x_363, 3);
lean_inc(x_393);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 lean_ctor_release(x_363, 2);
 lean_ctor_release(x_363, 3);
 x_394 = x_363;
} else {
 lean_dec_ref(x_363);
 x_394 = lean_box(0);
}
x_395 = lean_ctor_get(x_365, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_365, 1);
lean_inc(x_396);
x_397 = lean_ctor_get(x_365, 2);
lean_inc(x_397);
x_398 = lean_ctor_get(x_365, 3);
lean_inc(x_398);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 x_399 = x_365;
} else {
 lean_dec_ref(x_365);
 x_399 = lean_box(0);
}
x_400 = 1;
if (lean_is_scalar(x_399)) {
 x_401 = lean_alloc_ctor(1, 4, 1);
} else {
 x_401 = x_399;
}
lean_ctor_set(x_401, 0, x_355);
lean_ctor_set(x_401, 1, x_356);
lean_ctor_set(x_401, 2, x_357);
lean_ctor_set(x_401, 3, x_395);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
if (lean_is_scalar(x_394)) {
 x_402 = lean_alloc_ctor(1, 4, 1);
} else {
 x_402 = x_394;
}
lean_ctor_set(x_402, 0, x_398);
lean_ctor_set(x_402, 1, x_391);
lean_ctor_set(x_402, 2, x_392);
lean_ctor_set(x_402, 3, x_393);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_400);
x_403 = 0;
x_404 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_404, 0, x_401);
lean_ctor_set(x_404, 1, x_396);
lean_ctor_set(x_404, 2, x_397);
lean_ctor_set(x_404, 3, x_402);
lean_ctor_set_uint8(x_404, sizeof(void*)*4, x_403);
return x_404;
}
else
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_363, 3);
lean_inc(x_405);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; uint8_t x_407; lean_object* x_408; 
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 x_406 = x_365;
} else {
 lean_dec_ref(x_365);
 x_406 = lean_box(0);
}
x_407 = 1;
if (lean_is_scalar(x_406)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_406;
}
lean_ctor_set(x_408, 0, x_355);
lean_ctor_set(x_408, 1, x_356);
lean_ctor_set(x_408, 2, x_357);
lean_ctor_set(x_408, 3, x_363);
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_407);
return x_408;
}
else
{
uint8_t x_409; 
x_409 = lean_ctor_get_uint8(x_405, sizeof(void*)*4);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; 
x_410 = lean_ctor_get(x_363, 1);
lean_inc(x_410);
x_411 = lean_ctor_get(x_363, 2);
lean_inc(x_411);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 lean_ctor_release(x_363, 2);
 lean_ctor_release(x_363, 3);
 x_412 = x_363;
} else {
 lean_dec_ref(x_363);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_405, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_405, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_405, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_405, 3);
lean_inc(x_416);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 x_417 = x_405;
} else {
 lean_dec_ref(x_405);
 x_417 = lean_box(0);
}
x_418 = 1;
lean_inc(x_365);
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_355);
lean_ctor_set(x_419, 1, x_356);
lean_ctor_set(x_419, 2, x_357);
lean_ctor_set(x_419, 3, x_365);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 x_420 = x_365;
} else {
 lean_dec_ref(x_365);
 x_420 = lean_box(0);
}
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 4, 1);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_413);
lean_ctor_set(x_421, 1, x_414);
lean_ctor_set(x_421, 2, x_415);
lean_ctor_set(x_421, 3, x_416);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_418);
x_422 = 0;
if (lean_is_scalar(x_412)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_412;
}
lean_ctor_set(x_423, 0, x_419);
lean_ctor_set(x_423, 1, x_410);
lean_ctor_set(x_423, 2, x_411);
lean_ctor_set(x_423, 3, x_421);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; 
x_424 = lean_ctor_get(x_363, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_363, 2);
lean_inc(x_425);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 lean_ctor_release(x_363, 2);
 lean_ctor_release(x_363, 3);
 x_426 = x_363;
} else {
 lean_dec_ref(x_363);
 x_426 = lean_box(0);
}
x_427 = lean_ctor_get(x_365, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_365, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_365, 2);
lean_inc(x_429);
x_430 = lean_ctor_get(x_365, 3);
lean_inc(x_430);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 x_431 = x_365;
} else {
 lean_dec_ref(x_365);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 4, 1);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_427);
lean_ctor_set(x_432, 1, x_428);
lean_ctor_set(x_432, 2, x_429);
lean_ctor_set(x_432, 3, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*4, x_409);
if (lean_is_scalar(x_426)) {
 x_433 = lean_alloc_ctor(1, 4, 1);
} else {
 x_433 = x_426;
}
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_424);
lean_ctor_set(x_433, 2, x_425);
lean_ctor_set(x_433, 3, x_405);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_364);
x_434 = 1;
x_435 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_435, 0, x_355);
lean_ctor_set(x_435, 1, x_356);
lean_ctor_set(x_435, 2, x_357);
lean_ctor_set(x_435, 3, x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
return x_435;
}
}
}
}
}
else
{
uint8_t x_436; lean_object* x_437; 
x_436 = 1;
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_355);
lean_ctor_set(x_437, 1, x_356);
lean_ctor_set(x_437, 2, x_357);
lean_ctor_set(x_437, 3, x_363);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_436);
return x_437;
}
}
else
{
uint8_t x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_357);
lean_dec(x_356);
x_438 = 1;
x_439 = lean_box_uint64(x_2);
x_440 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_440, 0, x_355);
lean_ctor_set(x_440, 1, x_439);
lean_ctor_set(x_440, 2, x_3);
lean_ctor_set(x_440, 3, x_358);
lean_ctor_set_uint8(x_440, sizeof(void*)*4, x_438);
return x_440;
}
}
else
{
lean_object* x_441; uint8_t x_442; 
x_441 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_355, x_2, x_3);
x_442 = lean_ctor_get_uint8(x_441, sizeof(void*)*4);
if (x_442 == 0)
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_441, 0);
lean_inc(x_443);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; 
x_444 = lean_ctor_get(x_441, 3);
lean_inc(x_444);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; 
x_445 = lean_ctor_get(x_441, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_441, 2);
lean_inc(x_446);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 lean_ctor_release(x_441, 2);
 lean_ctor_release(x_441, 3);
 x_447 = x_441;
} else {
 lean_dec_ref(x_441);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_444);
lean_ctor_set(x_448, 1, x_445);
lean_ctor_set(x_448, 2, x_446);
lean_ctor_set(x_448, 3, x_444);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_442);
x_449 = 1;
x_450 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_356);
lean_ctor_set(x_450, 2, x_357);
lean_ctor_set(x_450, 3, x_358);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
return x_450;
}
else
{
uint8_t x_451; 
x_451 = lean_ctor_get_uint8(x_444, sizeof(void*)*4);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; 
x_452 = lean_ctor_get(x_441, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_441, 2);
lean_inc(x_453);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 lean_ctor_release(x_441, 2);
 lean_ctor_release(x_441, 3);
 x_454 = x_441;
} else {
 lean_dec_ref(x_441);
 x_454 = lean_box(0);
}
x_455 = lean_ctor_get(x_444, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_444, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_444, 2);
lean_inc(x_457);
x_458 = lean_ctor_get(x_444, 3);
lean_inc(x_458);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 lean_ctor_release(x_444, 2);
 lean_ctor_release(x_444, 3);
 x_459 = x_444;
} else {
 lean_dec_ref(x_444);
 x_459 = lean_box(0);
}
x_460 = 1;
if (lean_is_scalar(x_459)) {
 x_461 = lean_alloc_ctor(1, 4, 1);
} else {
 x_461 = x_459;
}
lean_ctor_set(x_461, 0, x_443);
lean_ctor_set(x_461, 1, x_452);
lean_ctor_set(x_461, 2, x_453);
lean_ctor_set(x_461, 3, x_455);
lean_ctor_set_uint8(x_461, sizeof(void*)*4, x_460);
if (lean_is_scalar(x_454)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_454;
}
lean_ctor_set(x_462, 0, x_458);
lean_ctor_set(x_462, 1, x_356);
lean_ctor_set(x_462, 2, x_357);
lean_ctor_set(x_462, 3, x_358);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_460);
x_463 = 0;
x_464 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_464, 0, x_461);
lean_ctor_set(x_464, 1, x_456);
lean_ctor_set(x_464, 2, x_457);
lean_ctor_set(x_464, 3, x_462);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_463);
return x_464;
}
else
{
lean_object* x_465; uint8_t x_466; lean_object* x_467; 
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 lean_ctor_release(x_444, 2);
 lean_ctor_release(x_444, 3);
 x_465 = x_444;
} else {
 lean_dec_ref(x_444);
 x_465 = lean_box(0);
}
x_466 = 1;
if (lean_is_scalar(x_465)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_465;
}
lean_ctor_set(x_467, 0, x_441);
lean_ctor_set(x_467, 1, x_356);
lean_ctor_set(x_467, 2, x_357);
lean_ctor_set(x_467, 3, x_358);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_466);
return x_467;
}
}
}
else
{
uint8_t x_468; 
x_468 = lean_ctor_get_uint8(x_443, sizeof(void*)*4);
if (x_468 == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; 
x_469 = lean_ctor_get(x_441, 1);
lean_inc(x_469);
x_470 = lean_ctor_get(x_441, 2);
lean_inc(x_470);
x_471 = lean_ctor_get(x_441, 3);
lean_inc(x_471);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 lean_ctor_release(x_441, 2);
 lean_ctor_release(x_441, 3);
 x_472 = x_441;
} else {
 lean_dec_ref(x_441);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_443, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_443, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_443, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_443, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 lean_ctor_release(x_443, 2);
 lean_ctor_release(x_443, 3);
 x_477 = x_443;
} else {
 lean_dec_ref(x_443);
 x_477 = lean_box(0);
}
x_478 = 1;
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(1, 4, 1);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_473);
lean_ctor_set(x_479, 1, x_474);
lean_ctor_set(x_479, 2, x_475);
lean_ctor_set(x_479, 3, x_476);
lean_ctor_set_uint8(x_479, sizeof(void*)*4, x_478);
if (lean_is_scalar(x_472)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_472;
}
lean_ctor_set(x_480, 0, x_471);
lean_ctor_set(x_480, 1, x_356);
lean_ctor_set(x_480, 2, x_357);
lean_ctor_set(x_480, 3, x_358);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_478);
x_481 = 0;
x_482 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_469);
lean_ctor_set(x_482, 2, x_470);
lean_ctor_set(x_482, 3, x_480);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_481);
return x_482;
}
else
{
lean_object* x_483; 
x_483 = lean_ctor_get(x_441, 3);
lean_inc(x_483);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; uint8_t x_485; lean_object* x_486; 
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 lean_ctor_release(x_443, 2);
 lean_ctor_release(x_443, 3);
 x_484 = x_443;
} else {
 lean_dec_ref(x_443);
 x_484 = lean_box(0);
}
x_485 = 1;
if (lean_is_scalar(x_484)) {
 x_486 = lean_alloc_ctor(1, 4, 1);
} else {
 x_486 = x_484;
}
lean_ctor_set(x_486, 0, x_441);
lean_ctor_set(x_486, 1, x_356);
lean_ctor_set(x_486, 2, x_357);
lean_ctor_set(x_486, 3, x_358);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
uint8_t x_487; 
x_487 = lean_ctor_get_uint8(x_483, sizeof(void*)*4);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; 
x_488 = lean_ctor_get(x_441, 1);
lean_inc(x_488);
x_489 = lean_ctor_get(x_441, 2);
lean_inc(x_489);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 lean_ctor_release(x_441, 2);
 lean_ctor_release(x_441, 3);
 x_490 = x_441;
} else {
 lean_dec_ref(x_441);
 x_490 = lean_box(0);
}
x_491 = lean_ctor_get(x_483, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_483, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_483, 2);
lean_inc(x_493);
x_494 = lean_ctor_get(x_483, 3);
lean_inc(x_494);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 lean_ctor_release(x_483, 2);
 lean_ctor_release(x_483, 3);
 x_495 = x_483;
} else {
 lean_dec_ref(x_483);
 x_495 = lean_box(0);
}
x_496 = 1;
lean_inc(x_443);
if (lean_is_scalar(x_495)) {
 x_497 = lean_alloc_ctor(1, 4, 1);
} else {
 x_497 = x_495;
}
lean_ctor_set(x_497, 0, x_443);
lean_ctor_set(x_497, 1, x_488);
lean_ctor_set(x_497, 2, x_489);
lean_ctor_set(x_497, 3, x_491);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 lean_ctor_release(x_443, 2);
 lean_ctor_release(x_443, 3);
 x_498 = x_443;
} else {
 lean_dec_ref(x_443);
 x_498 = lean_box(0);
}
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_496);
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(1, 4, 1);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_494);
lean_ctor_set(x_499, 1, x_356);
lean_ctor_set(x_499, 2, x_357);
lean_ctor_set(x_499, 3, x_358);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_496);
x_500 = 0;
if (lean_is_scalar(x_490)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_490;
}
lean_ctor_set(x_501, 0, x_497);
lean_ctor_set(x_501, 1, x_492);
lean_ctor_set(x_501, 2, x_493);
lean_ctor_set(x_501, 3, x_499);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
return x_501;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; lean_object* x_513; 
x_502 = lean_ctor_get(x_441, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_441, 2);
lean_inc(x_503);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 lean_ctor_release(x_441, 2);
 lean_ctor_release(x_441, 3);
 x_504 = x_441;
} else {
 lean_dec_ref(x_441);
 x_504 = lean_box(0);
}
x_505 = lean_ctor_get(x_443, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_443, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_443, 2);
lean_inc(x_507);
x_508 = lean_ctor_get(x_443, 3);
lean_inc(x_508);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 lean_ctor_release(x_443, 2);
 lean_ctor_release(x_443, 3);
 x_509 = x_443;
} else {
 lean_dec_ref(x_443);
 x_509 = lean_box(0);
}
if (lean_is_scalar(x_509)) {
 x_510 = lean_alloc_ctor(1, 4, 1);
} else {
 x_510 = x_509;
}
lean_ctor_set(x_510, 0, x_505);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set(x_510, 2, x_507);
lean_ctor_set(x_510, 3, x_508);
lean_ctor_set_uint8(x_510, sizeof(void*)*4, x_487);
if (lean_is_scalar(x_504)) {
 x_511 = lean_alloc_ctor(1, 4, 1);
} else {
 x_511 = x_504;
}
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_502);
lean_ctor_set(x_511, 2, x_503);
lean_ctor_set(x_511, 3, x_483);
lean_ctor_set_uint8(x_511, sizeof(void*)*4, x_442);
x_512 = 1;
x_513 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_356);
lean_ctor_set(x_513, 2, x_357);
lean_ctor_set(x_513, 3, x_358);
lean_ctor_set_uint8(x_513, sizeof(void*)*4, x_512);
return x_513;
}
}
}
}
}
else
{
uint8_t x_514; lean_object* x_515; 
x_514 = 1;
x_515 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_515, 0, x_441);
lean_ctor_set(x_515, 1, x_356);
lean_ctor_set(x_515, 2, x_357);
lean_ctor_set(x_515, 3, x_358);
lean_ctor_set_uint8(x_515, sizeof(void*)*4, x_514);
return x_515;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1(lean_object* x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_RpcSession_new(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_st_mk_ref(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_12, 3);
x_16 = lean_unbox_uint64(x_6);
x_17 = l_Lean_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1(x_15, x_16, x_9);
lean_ctor_set(x_12, 3, x_17);
x_18 = lean_st_ref_set(x_1, x_12, x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_ctor_get(x_12, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_27 = lean_unbox_uint64(x_6);
x_28 = l_Lean_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1(x_26, x_27, x_9);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_st_ref_set(x_1, x_29, x_13);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
return x_3;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_3);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleRpcConnect___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_handleRpcConnect___spec__2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_RBNode_insert___at_Lean_Server_FileWorker_handleRpcConnect___spec__1(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_handleRpcConnect___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRpcConnect___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_handleRpcConnect(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_parseParams___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Got param with wrong structure: ", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_parseParams___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Json_compress(x_2);
x_9 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_7);
lean_dec(x_7);
x_14 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_IO_throwServerError___rarg(x_15, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_parseParams___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_parseParams___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcKeepAliveParams____x40_Lean_Data_Lsp_Extra___hyg_2266_(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_1);
x_8 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcReleaseParams____x40_Lean_Data_Lsp_Extra___hyg_2036_(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_1);
x_8 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_141_(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_1);
x_8 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_702_(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_1);
x_8 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleNotification___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("textDocument/didChange", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleNotification___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/cancelRequest", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleNotification___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/rpc/release", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleNotification___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/rpc/keepAlive", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleNotification___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Got unsupported notification method: ", 37);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Server_FileWorker_handleNotification___closed__1;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Server_FileWorker_handleNotification___closed__2;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Server_FileWorker_handleNotification___closed__3;
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Server_FileWorker_handleNotification___closed__4;
x_13 = lean_string_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Server_FileWorker_handleNotification___closed__5;
x_15 = lean_string_append(x_14, x_1);
x_16 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_IO_throwServerError___rarg(x_17, x_5);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Server_FileWorker_handleRpcKeepAlive(x_20, x_3, x_4, x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Server_FileWorker_handleRpcRelease(x_28, x_3, x_4, x_29);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Server_FileWorker_handleCancelRequest(x_36, x_3, x_4, x_37);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Server_FileWorker_handleDidChange(x_44, x_3, x_4, x_45);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleNotification___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_handleNotification(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_2);
x_13 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151_(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_20);
lean_inc(x_2);
x_23 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151_(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
lean_inc(x_2);
x_37 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151_(x_2, x_34);
switch (x_37) {
case 0:
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_33, x_2, x_3);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_38, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
lean_ctor_set(x_38, 0, x_41);
x_45 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 1);
x_47 = lean_ctor_get(x_38, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_39);
x_49 = 1;
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_38, 1);
x_53 = lean_ctor_get(x_38, 2);
x_54 = lean_ctor_get(x_38, 3);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
x_59 = lean_ctor_get(x_41, 2);
x_60 = lean_ctor_get(x_41, 3);
x_61 = 1;
lean_ctor_set(x_41, 3, x_57);
lean_ctor_set(x_41, 2, x_53);
lean_ctor_set(x_41, 1, x_52);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_61);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_60);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_61);
x_62 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
x_65 = lean_ctor_get(x_41, 2);
x_66 = lean_ctor_get(x_41, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_67 = 1;
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_53);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_66);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_67);
x_69 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_70 = lean_ctor_get(x_38, 1);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_ctor_get(x_41, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_41, 3);
lean_inc(x_75);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_76 = x_41;
} else {
 lean_dec_ref(x_41);
 x_76 = lean_box(0);
}
x_77 = 1;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 4, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_40);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_77);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_35);
lean_ctor_set(x_79, 3, x_36);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_77);
x_80 = 0;
lean_ctor_set(x_1, 3, x_79);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_78);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_80);
return x_1;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_1);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_41, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_41, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_41, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_41, 0);
lean_dec(x_85);
x_86 = 1;
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_86);
return x_41;
}
else
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_41);
x_87 = 1;
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_35);
lean_ctor_set(x_88, 3, x_36);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_38);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_38, 1);
x_92 = lean_ctor_get(x_38, 2);
x_93 = lean_ctor_get(x_38, 3);
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_40);
if (x_95 == 0)
{
uint8_t x_96; uint8_t x_97; 
x_96 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_96);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_96);
x_97 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_40, 0);
x_99 = lean_ctor_get(x_40, 1);
x_100 = lean_ctor_get(x_40, 2);
x_101 = lean_ctor_get(x_40, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_40);
x_102 = 1;
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_102);
x_104 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_103);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_104);
return x_1;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_105 = lean_ctor_get(x_38, 1);
x_106 = lean_ctor_get(x_38, 2);
x_107 = lean_ctor_get(x_38, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_38);
x_108 = lean_ctor_get(x_40, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_112 = x_40;
} else {
 lean_dec_ref(x_40);
 x_112 = lean_box(0);
}
x_113 = 1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_34);
lean_ctor_set(x_115, 2, x_35);
lean_ctor_set(x_115, 3, x_36);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_113);
x_116 = 0;
lean_ctor_set(x_1, 3, x_115);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_116);
return x_1;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_38, 3);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_free_object(x_1);
x_118 = !lean_is_exclusive(x_40);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_40, 3);
lean_dec(x_119);
x_120 = lean_ctor_get(x_40, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_40, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_40, 0);
lean_dec(x_122);
x_123 = 1;
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_123);
return x_40;
}
else
{
uint8_t x_124; lean_object* x_125; 
lean_dec(x_40);
x_124 = 1;
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_38);
lean_ctor_set(x_125, 1, x_34);
lean_ctor_set(x_125, 2, x_35);
lean_ctor_set(x_125, 3, x_36);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_126 == 0)
{
uint8_t x_127; 
lean_free_object(x_1);
x_127 = !lean_is_exclusive(x_38);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_38, 1);
x_129 = lean_ctor_get(x_38, 2);
x_130 = lean_ctor_get(x_38, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_38, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_117);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_117, 0);
x_134 = lean_ctor_get(x_117, 1);
x_135 = lean_ctor_get(x_117, 2);
x_136 = lean_ctor_get(x_117, 3);
x_137 = 1;
lean_inc(x_40);
lean_ctor_set(x_117, 3, x_133);
lean_ctor_set(x_117, 2, x_129);
lean_ctor_set(x_117, 1, x_128);
lean_ctor_set(x_117, 0, x_40);
x_138 = !lean_is_exclusive(x_40);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_40, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_40, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_40, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_40, 0);
lean_dec(x_142);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_136);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_137);
x_143 = 0;
lean_ctor_set(x_38, 3, x_40);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_143);
return x_38;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_40);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_34);
lean_ctor_set(x_144, 2, x_35);
lean_ctor_set(x_144, 3, x_36);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_137);
x_145 = 0;
lean_ctor_set(x_38, 3, x_144);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_145);
return x_38;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_146 = lean_ctor_get(x_117, 0);
x_147 = lean_ctor_get(x_117, 1);
x_148 = lean_ctor_get(x_117, 2);
x_149 = lean_ctor_get(x_117, 3);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_117);
x_150 = 1;
lean_inc(x_40);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_40);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set(x_151, 2, x_129);
lean_ctor_set(x_151, 3, x_146);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_152 = x_40;
} else {
 lean_dec_ref(x_40);
 x_152 = lean_box(0);
}
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 4, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_34);
lean_ctor_set(x_153, 2, x_35);
lean_ctor_set(x_153, 3, x_36);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_150);
x_154 = 0;
lean_ctor_set(x_38, 3, x_153);
lean_ctor_set(x_38, 2, x_148);
lean_ctor_set(x_38, 1, x_147);
lean_ctor_set(x_38, 0, x_151);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_154);
return x_38;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_38, 1);
x_156 = lean_ctor_get(x_38, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_38);
x_157 = lean_ctor_get(x_117, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_117, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_117, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_161 = x_117;
} else {
 lean_dec_ref(x_117);
 x_161 = lean_box(0);
}
x_162 = 1;
lean_inc(x_40);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_40);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_164 = x_40;
} else {
 lean_dec_ref(x_40);
 x_164 = lean_box(0);
}
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_162);
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_34);
lean_ctor_set(x_165, 2, x_35);
lean_ctor_set(x_165, 3, x_36);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_162);
x_166 = 0;
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_38);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_38, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_38, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_40);
if (x_171 == 0)
{
uint8_t x_172; 
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_126);
x_172 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_172);
return x_1;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_40, 0);
x_174 = lean_ctor_get(x_40, 1);
x_175 = lean_ctor_get(x_40, 2);
x_176 = lean_ctor_get(x_40, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_40);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_175);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_126);
lean_ctor_set(x_38, 0, x_177);
x_178 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_178);
return x_1;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_38, 1);
x_180 = lean_ctor_get(x_38, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_38);
x_181 = lean_ctor_get(x_40, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 3);
lean_inc(x_184);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_185 = x_40;
} else {
 lean_dec_ref(x_40);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 4, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_126);
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_117);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_39);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_189; 
x_189 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
case 1:
{
uint8_t x_190; 
lean_dec(x_35);
lean_dec(x_34);
x_190 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
default: 
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_36, x_2, x_3);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*4);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 3);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_191, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
lean_ctor_set(x_191, 0, x_194);
x_198 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_191, 1);
x_200 = lean_ctor_get(x_191, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_192);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_191);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_191, 1);
x_206 = lean_ctor_get(x_191, 2);
x_207 = lean_ctor_get(x_191, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_191, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_210 = lean_ctor_get(x_194, 0);
x_211 = lean_ctor_get(x_194, 1);
x_212 = lean_ctor_get(x_194, 2);
x_213 = lean_ctor_get(x_194, 3);
x_214 = 1;
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_214);
lean_ctor_set(x_191, 3, x_213);
lean_ctor_set(x_191, 2, x_212);
lean_ctor_set(x_191, 1, x_211);
lean_ctor_set(x_191, 0, x_210);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_214);
x_215 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_215);
return x_1;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_194, 0);
x_217 = lean_ctor_get(x_194, 1);
x_218 = lean_ctor_get(x_194, 2);
x_219 = lean_ctor_get(x_194, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_194);
x_220 = 1;
x_221 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_221, 0, x_33);
lean_ctor_set(x_221, 1, x_34);
lean_ctor_set(x_221, 2, x_35);
lean_ctor_set(x_221, 3, x_193);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_220);
lean_ctor_set(x_191, 3, x_219);
lean_ctor_set(x_191, 2, x_218);
lean_ctor_set(x_191, 1, x_217);
lean_ctor_set(x_191, 0, x_216);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_220);
x_222 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_222);
return x_1;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = lean_ctor_get(x_191, 1);
x_224 = lean_ctor_get(x_191, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_191);
x_225 = lean_ctor_get(x_194, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_194, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_194, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_194, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 4, 1);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_33);
lean_ctor_set(x_231, 1, x_34);
lean_ctor_set(x_231, 2, x_35);
lean_ctor_set(x_231, 3, x_193);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_230);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set(x_232, 2, x_227);
lean_ctor_set(x_232, 3, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_230);
x_233 = 0;
lean_ctor_set(x_1, 3, x_232);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_231);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_234; 
lean_free_object(x_1);
x_234 = !lean_is_exclusive(x_194);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_194, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_194, 2);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 1);
lean_dec(x_237);
x_238 = lean_ctor_get(x_194, 0);
lean_dec(x_238);
x_239 = 1;
lean_ctor_set(x_194, 3, x_191);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_239);
return x_194;
}
else
{
uint8_t x_240; lean_object* x_241; 
lean_dec(x_194);
x_240 = 1;
x_241 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_241, 0, x_33);
lean_ctor_set(x_241, 1, x_34);
lean_ctor_set(x_241, 2, x_35);
lean_ctor_set(x_241, 3, x_191);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
x_242 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_191);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_191, 0);
lean_dec(x_244);
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_193, 0);
x_247 = lean_ctor_get(x_193, 1);
x_248 = lean_ctor_get(x_193, 2);
x_249 = lean_ctor_get(x_193, 3);
x_250 = 1;
lean_ctor_set(x_193, 3, x_246);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_250);
lean_ctor_set(x_191, 0, x_249);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_250);
x_251 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_251);
return x_1;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_252 = lean_ctor_get(x_193, 0);
x_253 = lean_ctor_get(x_193, 1);
x_254 = lean_ctor_get(x_193, 2);
x_255 = lean_ctor_get(x_193, 3);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_193);
x_256 = 1;
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_33);
lean_ctor_set(x_257, 1, x_34);
lean_ctor_set(x_257, 2, x_35);
lean_ctor_set(x_257, 3, x_252);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_256);
lean_ctor_set(x_191, 0, x_255);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_256);
x_258 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_253);
lean_ctor_set(x_1, 0, x_257);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_258);
return x_1;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_259 = lean_ctor_get(x_191, 1);
x_260 = lean_ctor_get(x_191, 2);
x_261 = lean_ctor_get(x_191, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_191);
x_262 = lean_ctor_get(x_193, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_193, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_193, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_193, 3);
lean_inc(x_265);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_266 = x_193;
} else {
 lean_dec_ref(x_193);
 x_266 = lean_box(0);
}
x_267 = 1;
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(1, 4, 1);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_33);
lean_ctor_set(x_268, 1, x_34);
lean_ctor_set(x_268, 2, x_35);
lean_ctor_set(x_268, 3, x_262);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_267);
x_270 = 0;
lean_ctor_set(x_1, 3, x_269);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_191, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_free_object(x_1);
x_272 = !lean_is_exclusive(x_193);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_193, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_193, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_193, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_193, 0);
lean_dec(x_276);
x_277 = 1;
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_277);
return x_193;
}
else
{
uint8_t x_278; lean_object* x_279; 
lean_dec(x_193);
x_278 = 1;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_33);
lean_ctor_set(x_279, 1, x_34);
lean_ctor_set(x_279, 2, x_35);
lean_ctor_set(x_279, 3, x_191);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_191);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_191, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_191, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_271);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; 
x_285 = lean_ctor_get(x_271, 0);
x_286 = lean_ctor_get(x_271, 1);
x_287 = lean_ctor_get(x_271, 2);
x_288 = lean_ctor_get(x_271, 3);
x_289 = 1;
lean_inc(x_193);
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 2, x_35);
lean_ctor_set(x_271, 1, x_34);
lean_ctor_set(x_271, 0, x_33);
x_290 = !lean_is_exclusive(x_193);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_193, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_193, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_193, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_193, 0);
lean_dec(x_294);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
lean_ctor_set(x_193, 3, x_288);
lean_ctor_set(x_193, 2, x_287);
lean_ctor_set(x_193, 1, x_286);
lean_ctor_set(x_193, 0, x_285);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_289);
x_295 = 0;
lean_ctor_set(x_191, 3, x_193);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_295);
return x_191;
}
else
{
lean_object* x_296; uint8_t x_297; 
lean_dec(x_193);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_286);
lean_ctor_set(x_296, 2, x_287);
lean_ctor_set(x_296, 3, x_288);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_289);
x_297 = 0;
lean_ctor_set(x_191, 3, x_296);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_297);
return x_191;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_298 = lean_ctor_get(x_271, 0);
x_299 = lean_ctor_get(x_271, 1);
x_300 = lean_ctor_get(x_271, 2);
x_301 = lean_ctor_get(x_271, 3);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_271);
x_302 = 1;
lean_inc(x_193);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_33);
lean_ctor_set(x_303, 1, x_34);
lean_ctor_set(x_303, 2, x_35);
lean_ctor_set(x_303, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_304 = x_193;
} else {
 lean_dec_ref(x_193);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_302);
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 4, 1);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_299);
lean_ctor_set(x_305, 2, x_300);
lean_ctor_set(x_305, 3, x_301);
lean_ctor_set_uint8(x_305, sizeof(void*)*4, x_302);
x_306 = 0;
lean_ctor_set(x_191, 3, x_305);
lean_ctor_set(x_191, 0, x_303);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_306);
return x_191;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_307 = lean_ctor_get(x_191, 1);
x_308 = lean_ctor_get(x_191, 2);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_191);
x_309 = lean_ctor_get(x_271, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_271, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_271, 3);
lean_inc(x_312);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_313 = x_271;
} else {
 lean_dec_ref(x_271);
 x_313 = lean_box(0);
}
x_314 = 1;
lean_inc(x_193);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(1, 4, 1);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_33);
lean_ctor_set(x_315, 1, x_34);
lean_ctor_set(x_315, 2, x_35);
lean_ctor_set(x_315, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_316 = x_193;
} else {
 lean_dec_ref(x_193);
 x_316 = lean_box(0);
}
lean_ctor_set_uint8(x_315, sizeof(void*)*4, x_314);
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 4, 1);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_310);
lean_ctor_set(x_317, 2, x_311);
lean_ctor_set(x_317, 3, x_312);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_314);
x_318 = 0;
x_319 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_307);
lean_ctor_set(x_319, 2, x_308);
lean_ctor_set(x_319, 3, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_318);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_191);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_191, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_191, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
uint8_t x_324; 
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_280);
x_324 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_324);
return x_1;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_193, 0);
x_326 = lean_ctor_get(x_193, 1);
x_327 = lean_ctor_get(x_193, 2);
x_328 = lean_ctor_get(x_193, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_193);
x_329 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_329, 0, x_325);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set(x_329, 2, x_327);
lean_ctor_set(x_329, 3, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_280);
lean_ctor_set(x_191, 0, x_329);
x_330 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_330);
return x_1;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_331 = lean_ctor_get(x_191, 1);
x_332 = lean_ctor_get(x_191, 2);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_191);
x_333 = lean_ctor_get(x_193, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_193, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_193, 3);
lean_inc(x_336);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_337 = x_193;
} else {
 lean_dec_ref(x_193);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_334);
lean_ctor_set(x_338, 2, x_335);
lean_ctor_set(x_338, 3, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_280);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
lean_ctor_set(x_339, 2, x_332);
lean_ctor_set(x_339, 3, x_271);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_192);
x_340 = 1;
lean_ctor_set(x_1, 3, x_339);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_340);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_341; 
x_341 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_341);
return x_1;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_342 = lean_ctor_get(x_1, 0);
x_343 = lean_ctor_get(x_1, 1);
x_344 = lean_ctor_get(x_1, 2);
x_345 = lean_ctor_get(x_1, 3);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_1);
lean_inc(x_343);
lean_inc(x_2);
x_346 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_ordRequestID____x40_Lean_Data_JsonRpc___hyg_151_(x_2, x_343);
switch (x_346) {
case 0:
{
lean_object* x_347; uint8_t x_348; 
x_347 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_342, x_2, x_3);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_347, 3);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_353 = x_347;
} else {
 lean_dec_ref(x_347);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_348);
x_355 = 1;
x_356 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_343);
lean_ctor_set(x_356, 2, x_344);
lean_ctor_set(x_356, 3, x_345);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
return x_356;
}
else
{
uint8_t x_357; 
x_357 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_347, 2);
lean_inc(x_359);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_360 = x_347;
} else {
 lean_dec_ref(x_347);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_350, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_350, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_350, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_350, 3);
lean_inc(x_364);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_365 = x_350;
} else {
 lean_dec_ref(x_350);
 x_365 = lean_box(0);
}
x_366 = 1;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_349);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_359);
lean_ctor_set(x_367, 3, x_361);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
if (lean_is_scalar(x_360)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_360;
}
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set(x_368, 1, x_343);
lean_ctor_set(x_368, 2, x_344);
lean_ctor_set(x_368, 3, x_345);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_366);
x_369 = 0;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_362);
lean_ctor_set(x_370, 2, x_363);
lean_ctor_set(x_370, 3, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; uint8_t x_372; lean_object* x_373; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_371 = x_350;
} else {
 lean_dec_ref(x_350);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_347);
lean_ctor_set(x_373, 1, x_343);
lean_ctor_set(x_373, 2, x_344);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
x_374 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_375 = lean_ctor_get(x_347, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_347, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_347, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_378 = x_347;
} else {
 lean_dec_ref(x_347);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_349, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_349, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_383 = x_349;
} else {
 lean_dec_ref(x_349);
 x_383 = lean_box(0);
}
x_384 = 1;
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(1, 4, 1);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_379);
lean_ctor_set(x_385, 1, x_380);
lean_ctor_set(x_385, 2, x_381);
lean_ctor_set(x_385, 3, x_382);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
if (lean_is_scalar(x_378)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_378;
}
lean_ctor_set(x_386, 0, x_377);
lean_ctor_set(x_386, 1, x_343);
lean_ctor_set(x_386, 2, x_344);
lean_ctor_set(x_386, 3, x_345);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_384);
x_387 = 0;
x_388 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_375);
lean_ctor_set(x_388, 2, x_376);
lean_ctor_set(x_388, 3, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_347, 3);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_390 = x_349;
} else {
 lean_dec_ref(x_349);
 x_390 = lean_box(0);
}
x_391 = 1;
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_347);
lean_ctor_set(x_392, 1, x_343);
lean_ctor_set(x_392, 2, x_344);
lean_ctor_set(x_392, 3, x_345);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
uint8_t x_393; 
x_393 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_394 = lean_ctor_get(x_347, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_347, 2);
lean_inc(x_395);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_396 = x_347;
} else {
 lean_dec_ref(x_347);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_389, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_389, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_389, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_389, 3);
lean_inc(x_400);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_401 = x_389;
} else {
 lean_dec_ref(x_389);
 x_401 = lean_box(0);
}
x_402 = 1;
lean_inc(x_349);
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_349);
lean_ctor_set(x_403, 1, x_394);
lean_ctor_set(x_403, 2, x_395);
lean_ctor_set(x_403, 3, x_397);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_404 = x_349;
} else {
 lean_dec_ref(x_349);
 x_404 = lean_box(0);
}
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_400);
lean_ctor_set(x_405, 1, x_343);
lean_ctor_set(x_405, 2, x_344);
lean_ctor_set(x_405, 3, x_345);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_402);
x_406 = 0;
if (lean_is_scalar(x_396)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_396;
}
lean_ctor_set(x_407, 0, x_403);
lean_ctor_set(x_407, 1, x_398);
lean_ctor_set(x_407, 2, x_399);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_408 = lean_ctor_get(x_347, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_347, 2);
lean_inc(x_409);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_410 = x_347;
} else {
 lean_dec_ref(x_347);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_349, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_349, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_415 = x_349;
} else {
 lean_dec_ref(x_349);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 4, 1);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_412);
lean_ctor_set(x_416, 2, x_413);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_393);
if (lean_is_scalar(x_410)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_410;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_408);
lean_ctor_set(x_417, 2, x_409);
lean_ctor_set(x_417, 3, x_389);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_348);
x_418 = 1;
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_343);
lean_ctor_set(x_419, 2, x_344);
lean_ctor_set(x_419, 3, x_345);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
return x_419;
}
}
}
}
}
else
{
uint8_t x_420; lean_object* x_421; 
x_420 = 1;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_347);
lean_ctor_set(x_421, 1, x_343);
lean_ctor_set(x_421, 2, x_344);
lean_ctor_set(x_421, 3, x_345);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
}
case 1:
{
uint8_t x_422; lean_object* x_423; 
lean_dec(x_344);
lean_dec(x_343);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_342);
lean_ctor_set(x_423, 1, x_2);
lean_ctor_set(x_423, 2, x_3);
lean_ctor_set(x_423, 3, x_345);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
default: 
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_345, x_2, x_3);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_424, 3);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_424, 2);
lean_inc(x_429);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_430 = x_424;
} else {
 lean_dec_ref(x_424);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_429);
lean_ctor_set(x_431, 3, x_427);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_425);
x_432 = 1;
x_433 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_433, 0, x_342);
lean_ctor_set(x_433, 1, x_343);
lean_ctor_set(x_433, 2, x_344);
lean_ctor_set(x_433, 3, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_432);
return x_433;
}
else
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_424, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_437 = x_424;
} else {
 lean_dec_ref(x_424);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_427, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_427, 3);
lean_inc(x_441);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_442 = x_427;
} else {
 lean_dec_ref(x_427);
 x_442 = lean_box(0);
}
x_443 = 1;
if (lean_is_scalar(x_442)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_442;
}
lean_ctor_set(x_444, 0, x_342);
lean_ctor_set(x_444, 1, x_343);
lean_ctor_set(x_444, 2, x_344);
lean_ctor_set(x_444, 3, x_426);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_438);
lean_ctor_set(x_445, 1, x_439);
lean_ctor_set(x_445, 2, x_440);
lean_ctor_set(x_445, 3, x_441);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_443);
x_446 = 0;
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_435);
lean_ctor_set(x_447, 2, x_436);
lean_ctor_set(x_447, 3, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_446);
return x_447;
}
else
{
lean_object* x_448; uint8_t x_449; lean_object* x_450; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_448 = x_427;
} else {
 lean_dec_ref(x_427);
 x_448 = lean_box(0);
}
x_449 = 1;
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_342);
lean_ctor_set(x_450, 1, x_343);
lean_ctor_set(x_450, 2, x_344);
lean_ctor_set(x_450, 3, x_424);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
x_451 = lean_ctor_get_uint8(x_426, sizeof(void*)*4);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_452 = lean_ctor_get(x_424, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_424, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_424, 3);
lean_inc(x_454);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_455 = x_424;
} else {
 lean_dec_ref(x_424);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_426, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_426, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_426, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_426, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_460 = x_426;
} else {
 lean_dec_ref(x_426);
 x_460 = lean_box(0);
}
x_461 = 1;
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_342);
lean_ctor_set(x_462, 1, x_343);
lean_ctor_set(x_462, 2, x_344);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_455)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_455;
}
lean_ctor_set(x_463, 0, x_459);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_453);
lean_ctor_set(x_463, 3, x_454);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_461);
x_464 = 0;
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_457);
lean_ctor_set(x_465, 2, x_458);
lean_ctor_set(x_465, 3, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_464);
return x_465;
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_424, 3);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; uint8_t x_468; lean_object* x_469; 
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_467 = x_426;
} else {
 lean_dec_ref(x_426);
 x_467 = lean_box(0);
}
x_468 = 1;
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_342);
lean_ctor_set(x_469, 1, x_343);
lean_ctor_set(x_469, 2, x_344);
lean_ctor_set(x_469, 3, x_424);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
uint8_t x_470; 
x_470 = lean_ctor_get_uint8(x_466, sizeof(void*)*4);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_471 = lean_ctor_get(x_424, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_424, 2);
lean_inc(x_472);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_473 = x_424;
} else {
 lean_dec_ref(x_424);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_466, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_466, 3);
lean_inc(x_477);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 x_478 = x_466;
} else {
 lean_dec_ref(x_466);
 x_478 = lean_box(0);
}
x_479 = 1;
lean_inc(x_426);
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_342);
lean_ctor_set(x_480, 1, x_343);
lean_ctor_set(x_480, 2, x_344);
lean_ctor_set(x_480, 3, x_426);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_481 = x_426;
} else {
 lean_dec_ref(x_426);
 x_481 = lean_box(0);
}
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 4, 1);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_474);
lean_ctor_set(x_482, 1, x_475);
lean_ctor_set(x_482, 2, x_476);
lean_ctor_set(x_482, 3, x_477);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_479);
x_483 = 0;
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_473;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_471);
lean_ctor_set(x_484, 2, x_472);
lean_ctor_set(x_484, 3, x_482);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; 
x_485 = lean_ctor_get(x_424, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_424, 2);
lean_inc(x_486);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_487 = x_424;
} else {
 lean_dec_ref(x_424);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_426, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_426, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_426, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_426, 3);
lean_inc(x_491);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_492 = x_426;
} else {
 lean_dec_ref(x_426);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_489);
lean_ctor_set(x_493, 2, x_490);
lean_ctor_set(x_493, 3, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_470);
if (lean_is_scalar(x_487)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_487;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_485);
lean_ctor_set(x_494, 2, x_486);
lean_ctor_set(x_494, 3, x_466);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_425);
x_495 = 1;
x_496 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_496, 0, x_342);
lean_ctor_set(x_496, 1, x_343);
lean_ctor_set(x_496, 2, x_344);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*4, x_495);
return x_496;
}
}
}
}
}
else
{
uint8_t x_497; lean_object* x_498; 
x_497 = 1;
x_498 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_498, 0, x_342);
lean_ctor_set(x_498, 1, x_343);
lean_ctor_set(x_498, 2, x_344);
lean_ctor_set(x_498, 3, x_424);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_497);
return x_498;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Server_FileWorker_queueRequest___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lean_Server_FileWorker_queueRequest___spec__2(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_insert___at_Lean_Server_FileWorker_queueRequest___spec__1(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_queueRequest___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = l_Lean_Server_FileWorker_updatePendingRequests(x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_queueRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_queueRequest(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at_Lean_Server_FileWorker_handleRequest___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_io_error_to_string(x_3);
x_5 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_IO_FS_Stream_writeLspMessage(x_1, x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonRpcConnectParams____x40_Lean_Data_Lsp_Extra___hyg_1446_(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Json_compress(x_1);
x_8 = l_Lean_Server_FileWorker_parseParams___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_parseParams___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
lean_dec(x_6);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_throwServerError___rarg(x_14, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_7 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_toJsonRpcConnected____x40_Lean_Data_Lsp_Extra___hyg_1626_(x_6);
x_8 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lean_Server_RequestError_toLspResponseError(x_1, x_6);
lean_dec(x_6);
x_8 = l_IO_FS_Stream_writeLspResponseError(x_2, x_7, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_10);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = l_Lean_Server_RequestError_toLspResponseError(x_1, x_19);
lean_dec(x_19);
x_21 = l_IO_FS_Stream_writeLspResponseError(x_2, x_20, x_4);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
 lean_ctor_set_tag(x_31, 0);
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__2(x_2, x_34, x_4);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_3, 0, x_37);
lean_ctor_set(x_35, 0, x_3);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_3, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_35, 0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_42);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_3);
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
lean_dec(x_3);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__2(x_2, x_47, x_4);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_49);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_54);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
 lean_ctor_set_tag(x_58, 0);
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_IO_ofExcept___at_Lean_Server_FileWorker_handleRequest___spec__1(x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_37 = lean_ctor_get(x_2, 4);
lean_inc(x_37);
lean_dec(x_2);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_11);
lean_ctor_set(x_38, 2, x_13);
lean_ctor_set(x_38, 3, x_14);
lean_ctor_set(x_38, 4, x_15);
lean_ctor_set(x_38, 5, x_37);
x_39 = l_Lean_Server_handleLspRequest(x_4, x_5, x_38, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_40);
x_16 = x_42;
x_17 = x_41;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_16 = x_45;
x_17 = x_44;
goto block_36;
}
block_36:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Server_RequestError_toLspResponseError(x_3, x_18);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l_IO_FS_Stream_writeLspResponseError___boxed), 3, 2);
lean_closure_set(x_20, 0, x_15);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_EIO_toBaseIO___rarg), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = l_Task_Priority_default;
x_23 = lean_io_as_task(x_21, x_22, x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleRequest___lambda__1), 4, 2);
lean_closure_set(x_29, 0, x_3);
lean_closure_set(x_29, 1, x_15);
x_30 = l_Task_Priority_default;
x_31 = lean_io_map_task(x_29, x_28, x_30, x_17);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_8, 0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_task_pure(x_48);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_49);
return x_8;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_task_pure(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_handleRequest___lambda__2___boxed), 7, 5);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
x_12 = l_Task_Priority_default;
x_13 = lean_io_bind_task(x_10, x_11, x_12, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Server_FileWorker_queueRequest(x_3, x_14, x_7, x_8, x_15);
return x_16;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleRequest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("$/lean/rpc/connect", 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Server_FileWorker_handleRequest___closed__1;
x_11 = lean_string_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
lean_inc(x_4);
x_13 = l_Lean_Server_FileWorker_handleRequest___lambda__3(x_4, x_8, x_1, x_2, x_3, x_12, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_2);
x_14 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__3(x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Server_FileWorker_handleRpcConnect___rarg(x_5, x_15);
lean_dec(x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_17);
lean_inc(x_19);
x_21 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__4(x_19, x_20, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_io_error_to_string(x_28);
x_31 = lean_box(0);
x_32 = 4;
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_32);
x_34 = l_IO_FS_Stream_writeLspResponseError(x_19, x_33, x_29);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_34, 0);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_16, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_dec(x_16);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
lean_dec(x_4);
x_48 = lean_io_error_to_string(x_45);
x_49 = lean_box(0);
x_50 = 4;
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_51, 2, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_50);
x_52 = l_IO_FS_Stream_writeLspResponseError(x_47, x_51, x_46);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
return x_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_5);
x_63 = lean_ctor_get(x_14, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_14, 1);
lean_inc(x_64);
lean_dec(x_14);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_dec(x_4);
x_66 = lean_io_error_to_string(x_63);
x_67 = lean_box(0);
x_68 = 4;
x_69 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_68);
x_70 = l_IO_FS_Stream_writeLspResponseError(x_65, x_69, x_64);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_70);
if (x_77 == 0)
{
return x_70;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_70, 0);
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_70);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_FileWorker_handleRequest___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_parseParams___at_Lean_Server_FileWorker_handleRequest___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_handleRequest___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleRequest___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_FileWorker_handleRequest___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_RBNode_erase___at_Lean_Server_FileWorker_handleCancelRequest___spec__1(x_1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\"", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Failed responding to request ", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2;
x_2 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5;
x_2 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(x_1, x_7, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_has_finished(x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_1 = x_12;
x_2 = x_10;
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_task_get_own(x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_io_error_to_string(x_21);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
lean_dec(x_8);
x_24 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_string_append(x_25, x_24);
x_27 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_22);
lean_dec(x_22);
x_32 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_IO_throwServerError___rarg(x_33, x_19);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
lean_dec(x_8);
x_40 = l_Lean_JsonNumber_toString(x_39);
x_41 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_string_append(x_44, x_22);
lean_dec(x_22);
x_46 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_IO_throwServerError___rarg(x_47, x_19);
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
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
default: 
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6;
x_54 = lean_string_append(x_53, x_22);
lean_dec(x_22);
x_55 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_56 = lean_string_append(x_54, x_55);
x_57 = l_IO_throwServerError___rarg(x_56, x_19);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_20);
x_62 = lean_box(0);
x_63 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1(x_8, x_12, x_62, x_19);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_1 = x_64;
x_2 = x_10;
x_5 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_67 = !lean_is_exclusive(x_11);
if (x_67 == 0)
{
return x_11;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_11, 0);
x_69 = lean_ctor_get(x_11, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_11);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_unbox_uint64(x_6);
x_10 = lean_uint64_dec_lt(x_1, x_9);
if (x_10 == 0)
{
uint64_t x_11; uint8_t x_12; 
x_11 = lean_unbox_uint64(x_6);
x_12 = lean_uint64_dec_eq(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_RBNode_isBlack___rarg(x_8);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_8);
x_15 = 0;
lean_ctor_set(x_2, 3, x_14);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_15);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_2);
x_16 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_8);
x_17 = l_Lean_RBNode_balRight___rarg(x_5, x_6, x_7, x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_18 = l_Lean_RBNode_appendTrees___rarg(x_5, x_8);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = l_Lean_RBNode_isBlack___rarg(x_5);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_5);
x_21 = 0;
lean_ctor_set(x_2, 0, x_20);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_21);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_2);
x_22 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_5);
x_23 = l_Lean_RBNode_balLeft___rarg(x_22, x_6, x_7, x_8);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
x_27 = lean_ctor_get(x_2, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_28 = lean_unbox_uint64(x_25);
x_29 = lean_uint64_dec_lt(x_1, x_28);
if (x_29 == 0)
{
uint64_t x_30; uint8_t x_31; 
x_30 = lean_unbox_uint64(x_25);
x_31 = lean_uint64_dec_eq(x_1, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_RBNode_isBlack___rarg(x_27);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_27);
x_34 = 0;
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_26);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_27);
x_37 = l_Lean_RBNode_balRight___rarg(x_24, x_25, x_26, x_36);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_26);
lean_dec(x_25);
x_38 = l_Lean_RBNode_appendTrees___rarg(x_24, x_27);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = l_Lean_RBNode_isBlack___rarg(x_24);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_24);
x_41 = 0;
x_42 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_26);
lean_ctor_set(x_42, 3, x_27);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_24);
x_44 = l_Lean_RBNode_balLeft___rarg(x_43, x_25, x_26, x_27);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4(x_1, x_9, x_3, x_4, x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_11, x_15);
lean_dec(x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Server_FileWorker_RpcSession_hasExpired(x_18, x_19);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_10);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_2 = x_12;
x_3 = x_16;
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; uint64_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 3);
x_28 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_29 = l_Lean_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(x_28, x_27);
lean_ctor_set(x_16, 3, x_29);
x_2 = x_12;
x_3 = x_16;
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
x_33 = lean_ctor_get(x_16, 2);
x_34 = lean_ctor_get(x_16, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_35 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_36 = l_Lean_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(x_35, x_34);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_33);
lean_ctor_set(x_37, 3, x_36);
x_2 = x_12;
x_3 = x_37;
x_6 = x_25;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(x_8, x_2, x_3, x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_10, x_14);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Server_FileWorker_RpcSession_hasExpired(x_17, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_9);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_1 = x_11;
x_2 = x_15;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; uint64_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 3);
x_27 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_28 = l_Lean_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(x_27, x_26);
lean_ctor_set(x_15, 3, x_28);
x_1 = x_11;
x_2 = x_15;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
x_32 = lean_ctor_get(x_15, 2);
x_33 = lean_ctor_get(x_15, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_34 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_35 = l_Lean_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(x_34, x_33);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_35);
x_1 = x_11;
x_2 = x_36;
x_5 = x_24;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_mainLoop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Got invalid JSON-RPC message", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_mainLoop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("exit", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_mainLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = l_IO_FS_Stream_readLspMessage(x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_101; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_101 = !lean_is_exclusive(x_5);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_5, 0);
x_103 = lean_ctor_get(x_5, 1);
x_104 = lean_ctor_get(x_5, 2);
x_105 = lean_ctor_get(x_5, 3);
lean_inc(x_104);
x_106 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(x_104, x_104, x_1, x_2, x_10);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_105);
lean_ctor_set(x_5, 2, x_107);
x_109 = l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(x_105, x_5, x_1, x_2, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
x_11 = x_112;
x_12 = x_111;
goto block_100;
}
else
{
uint8_t x_113; 
lean_free_object(x_5);
lean_dec(x_105);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_106);
if (x_113 == 0)
{
return x_106;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_106, 0);
x_115 = lean_ctor_get(x_106, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_106);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_5, 0);
x_118 = lean_ctor_get(x_5, 1);
x_119 = lean_ctor_get(x_5, 2);
x_120 = lean_ctor_get(x_5, 3);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_5);
lean_inc(x_119);
x_121 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(x_119, x_119, x_1, x_2, x_10);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_120);
x_124 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_124, 0, x_117);
lean_ctor_set(x_124, 1, x_118);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_120);
x_125 = l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(x_120, x_124, x_1, x_2, x_123);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_11 = x_128;
x_12 = x_127;
goto block_100;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_121, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_121, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_131 = x_121;
} else {
 lean_dec_ref(x_121);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
block_100:
{
lean_object* x_13; 
lean_inc(x_11);
x_13 = lean_st_ref_set(x_2, x_11, x_12);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Server_FileWorker_mainLoop___closed__1;
x_17 = l_IO_throwServerError___rarg(x_16, x_15);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_Server_FileWorker_handleRequest(x_20, x_21, x_23, x_1, x_2, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_3 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_dec(x_9);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_Lean_Server_FileWorker_handleRequest(x_32, x_33, x_35, x_1, x_2, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_3 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
case 1:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_dec(x_13);
x_44 = lean_ctor_get(x_9, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_dec(x_9);
x_46 = l_Lean_Server_FileWorker_mainLoop___closed__2;
x_47 = lean_string_dec_eq(x_44, x_46);
if (x_47 == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_44);
lean_dec(x_2);
lean_dec(x_1);
x_48 = l_Lean_Server_FileWorker_mainLoop___closed__1;
x_49 = l_IO_throwServerError___rarg(x_48, x_43);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_inc(x_2);
lean_inc(x_1);
x_53 = l_Lean_Server_FileWorker_handleNotification(x_44, x_52, x_1, x_2, x_43);
lean_dec(x_44);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_3 = x_54;
goto _start;
}
else
{
uint8_t x_56; 
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_50, 0);
lean_inc(x_60);
lean_dec(x_50);
x_61 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_inc(x_2);
lean_inc(x_1);
x_62 = l_Lean_Server_FileWorker_handleNotification(x_44, x_61, x_1, x_2, x_43);
lean_dec(x_44);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_3 = x_63;
goto _start;
}
else
{
uint8_t x_65; 
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_62);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
else
{
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_11, 0);
lean_inc(x_69);
lean_dec(x_11);
x_70 = lean_ctor_get(x_69, 2);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Server_FileWorker_CancelToken_set(x_70, x_43);
lean_dec(x_70);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_11);
x_78 = lean_ctor_get(x_45, 0);
lean_inc(x_78);
lean_dec(x_45);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_inc(x_2);
lean_inc(x_1);
x_81 = l_Lean_Server_FileWorker_handleNotification(x_46, x_80, x_1, x_2, x_43);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_3 = x_82;
goto _start;
}
else
{
uint8_t x_84; 
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_78, 0);
lean_inc(x_88);
lean_dec(x_78);
x_89 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_inc(x_2);
lean_inc(x_1);
x_90 = l_Lean_Server_FileWorker_handleNotification(x_46, x_89, x_1, x_2, x_43);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_3 = x_91;
goto _start;
}
else
{
uint8_t x_93; 
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_90);
if (x_93 == 0)
{
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_90);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
}
}
default: 
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_ctor_get(x_13, 1);
lean_inc(x_97);
lean_dec(x_13);
x_98 = l_Lean_Server_FileWorker_mainLoop___closed__1;
x_99 = l_IO_throwServerError___rarg(x_98, x_97);
return x_99;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_8);
if (x_133 == 0)
{
return x_8;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_8, 0);
x_135 = lean_ctor_get(x_8, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_8);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_RBNode_del___at_Lean_Server_FileWorker_mainLoop___spec__3(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_RBNode_erase___at_Lean_Server_FileWorker_mainLoop___spec__2(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_forIn_visit___at_Lean_Server_FileWorker_mainLoop___spec__4___at_Lean_Server_FileWorker_mainLoop___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected method '", 17);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', got method '", 15);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("processId", 9);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("clientInfo", 10);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rootUri", 7);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initializationOptions", 21);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("capabilities", 12);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unexpected param '", 18);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' for method '", 14);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'\n", 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trace", 5);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("workspaceFolders", 16);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("2.0", 3);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("jsonrpc", 7);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15;
x_2 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("method", 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("params", 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected JSON-RPC request, got: '", 33);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("result", 6);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("id", 2);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("message", 7);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("data", 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("code", 4);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error", 5);
return x_1;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__64;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__65;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32901u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__67;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__68;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__69;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__72() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__71;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__72;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__73;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readMessage(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_string_dec_eq(x_10, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_9);
x_13 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1;
x_14 = lean_string_append(x_13, x_3);
lean_dec(x_3);
x_15 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_10);
lean_dec(x_10);
x_18 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
if (lean_is_scalar(x_8)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_8;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_221; 
x_221 = lean_box(0);
x_22 = x_221;
goto block_220;
}
else
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_11, 0);
lean_inc(x_222);
lean_dec(x_11);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_22 = x_224;
goto block_220;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_22 = x_226;
goto block_220;
}
}
block_220:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3;
x_24 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(x_22, x_23);
x_25 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4;
x_26 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(x_22, x_25);
x_27 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5;
x_28 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_22, x_27);
x_29 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6;
x_30 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__3(x_22, x_29);
x_31 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7;
x_32 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4(x_22, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_9);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Json_compress(x_22);
x_35 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_3);
lean_dec(x_3);
x_40 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_string_append(x_41, x_33);
lean_dec(x_33);
x_43 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_8)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_8;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_32, 0);
lean_inc(x_47);
lean_dec(x_32);
x_48 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11;
x_49 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(x_22, x_48);
x_50 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12;
x_51 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__6(x_22, x_50);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_217; 
lean_dec(x_49);
x_217 = 0;
x_52 = x_217;
goto block_216;
}
else
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_49, 0);
lean_inc(x_218);
lean_dec(x_49);
x_219 = lean_unbox(x_218);
lean_dec(x_218);
x_52 = x_219;
goto block_216;
}
block_216:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_53; 
lean_dec(x_24);
x_53 = lean_box(0);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
x_54 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_47);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*6, x_52);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_9);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_54);
if (lean_is_scalar(x_8)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_8;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_59, 2, x_53);
lean_ctor_set(x_59, 3, x_53);
lean_ctor_set(x_59, 4, x_47);
lean_ctor_set(x_59, 5, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*6, x_52);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_9);
lean_ctor_set(x_60, 1, x_3);
lean_ctor_set(x_60, 2, x_59);
if (lean_is_scalar(x_8)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_8;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_30, 0);
lean_inc(x_62);
lean_dec(x_30);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_51);
x_64 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_53);
lean_ctor_set(x_64, 2, x_53);
lean_ctor_set(x_64, 3, x_63);
lean_ctor_set(x_64, 4, x_47);
lean_ctor_set(x_64, 5, x_53);
lean_ctor_set_uint8(x_64, sizeof(void*)*6, x_52);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_9);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 2, x_64);
if (lean_is_scalar(x_8)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_8;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_7);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
lean_dec(x_51);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_69, 0, x_53);
lean_ctor_set(x_69, 1, x_53);
lean_ctor_set(x_69, 2, x_53);
lean_ctor_set(x_69, 3, x_63);
lean_ctor_set(x_69, 4, x_47);
lean_ctor_set(x_69, 5, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*6, x_52);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_9);
lean_ctor_set(x_70, 1, x_3);
lean_ctor_set(x_70, 2, x_69);
if (lean_is_scalar(x_8)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_8;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_7);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_28, 0);
lean_inc(x_72);
lean_dec(x_28);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_51);
x_74 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_74, 0, x_53);
lean_ctor_set(x_74, 1, x_53);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_53);
lean_ctor_set(x_74, 4, x_47);
lean_ctor_set(x_74, 5, x_53);
lean_ctor_set_uint8(x_74, sizeof(void*)*6, x_52);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_9);
lean_ctor_set(x_75, 1, x_3);
lean_ctor_set(x_75, 2, x_74);
if (lean_is_scalar(x_8)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_8;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_7);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_51, 0);
lean_inc(x_77);
lean_dec(x_51);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_79, 0, x_53);
lean_ctor_set(x_79, 1, x_53);
lean_ctor_set(x_79, 2, x_73);
lean_ctor_set(x_79, 3, x_53);
lean_ctor_set(x_79, 4, x_47);
lean_ctor_set(x_79, 5, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*6, x_52);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_9);
lean_ctor_set(x_80, 1, x_3);
lean_ctor_set(x_80, 2, x_79);
if (lean_is_scalar(x_8)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_8;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_7);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_30, 0);
lean_inc(x_82);
lean_dec(x_30);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_51);
x_84 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_84, 0, x_53);
lean_ctor_set(x_84, 1, x_53);
lean_ctor_set(x_84, 2, x_73);
lean_ctor_set(x_84, 3, x_83);
lean_ctor_set(x_84, 4, x_47);
lean_ctor_set(x_84, 5, x_53);
lean_ctor_set_uint8(x_84, sizeof(void*)*6, x_52);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_9);
lean_ctor_set(x_85, 1, x_3);
lean_ctor_set(x_85, 2, x_84);
if (lean_is_scalar(x_8)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_8;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_7);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_51, 0);
lean_inc(x_87);
lean_dec(x_51);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_89, 0, x_53);
lean_ctor_set(x_89, 1, x_53);
lean_ctor_set(x_89, 2, x_73);
lean_ctor_set(x_89, 3, x_83);
lean_ctor_set(x_89, 4, x_47);
lean_ctor_set(x_89, 5, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*6, x_52);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_9);
lean_ctor_set(x_90, 1, x_3);
lean_ctor_set(x_90, 2, x_89);
if (lean_is_scalar(x_8)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_8;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_7);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_26, 0);
lean_inc(x_92);
lean_dec(x_26);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_51);
x_94 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_94, 0, x_53);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_53);
lean_ctor_set(x_94, 3, x_53);
lean_ctor_set(x_94, 4, x_47);
lean_ctor_set(x_94, 5, x_53);
lean_ctor_set_uint8(x_94, sizeof(void*)*6, x_52);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_9);
lean_ctor_set(x_95, 1, x_3);
lean_ctor_set(x_95, 2, x_94);
if (lean_is_scalar(x_8)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_8;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_7);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_51, 0);
lean_inc(x_97);
lean_dec(x_51);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_99, 0, x_53);
lean_ctor_set(x_99, 1, x_93);
lean_ctor_set(x_99, 2, x_53);
lean_ctor_set(x_99, 3, x_53);
lean_ctor_set(x_99, 4, x_47);
lean_ctor_set(x_99, 5, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*6, x_52);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_9);
lean_ctor_set(x_100, 1, x_3);
lean_ctor_set(x_100, 2, x_99);
if (lean_is_scalar(x_8)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_8;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_7);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_30, 0);
lean_inc(x_102);
lean_dec(x_30);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_51);
x_104 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_104, 0, x_53);
lean_ctor_set(x_104, 1, x_93);
lean_ctor_set(x_104, 2, x_53);
lean_ctor_set(x_104, 3, x_103);
lean_ctor_set(x_104, 4, x_47);
lean_ctor_set(x_104, 5, x_53);
lean_ctor_set_uint8(x_104, sizeof(void*)*6, x_52);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_9);
lean_ctor_set(x_105, 1, x_3);
lean_ctor_set(x_105, 2, x_104);
if (lean_is_scalar(x_8)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_8;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_7);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_51, 0);
lean_inc(x_107);
lean_dec(x_51);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_109, 0, x_53);
lean_ctor_set(x_109, 1, x_93);
lean_ctor_set(x_109, 2, x_53);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set(x_109, 4, x_47);
lean_ctor_set(x_109, 5, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*6, x_52);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_9);
lean_ctor_set(x_110, 1, x_3);
lean_ctor_set(x_110, 2, x_109);
if (lean_is_scalar(x_8)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_8;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_7);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_28, 0);
lean_inc(x_112);
lean_dec(x_28);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_51);
x_114 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_114, 0, x_53);
lean_ctor_set(x_114, 1, x_93);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_53);
lean_ctor_set(x_114, 4, x_47);
lean_ctor_set(x_114, 5, x_53);
lean_ctor_set_uint8(x_114, sizeof(void*)*6, x_52);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_9);
lean_ctor_set(x_115, 1, x_3);
lean_ctor_set(x_115, 2, x_114);
if (lean_is_scalar(x_8)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_8;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_7);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_51, 0);
lean_inc(x_117);
lean_dec(x_51);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_119, 0, x_53);
lean_ctor_set(x_119, 1, x_93);
lean_ctor_set(x_119, 2, x_113);
lean_ctor_set(x_119, 3, x_53);
lean_ctor_set(x_119, 4, x_47);
lean_ctor_set(x_119, 5, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*6, x_52);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_9);
lean_ctor_set(x_120, 1, x_3);
lean_ctor_set(x_120, 2, x_119);
if (lean_is_scalar(x_8)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_8;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_7);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_30, 0);
lean_inc(x_122);
lean_dec(x_30);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_51);
x_124 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_124, 0, x_53);
lean_ctor_set(x_124, 1, x_93);
lean_ctor_set(x_124, 2, x_113);
lean_ctor_set(x_124, 3, x_123);
lean_ctor_set(x_124, 4, x_47);
lean_ctor_set(x_124, 5, x_53);
lean_ctor_set_uint8(x_124, sizeof(void*)*6, x_52);
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_9);
lean_ctor_set(x_125, 1, x_3);
lean_ctor_set(x_125, 2, x_124);
if (lean_is_scalar(x_8)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_8;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_7);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_51, 0);
lean_inc(x_127);
lean_dec(x_51);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_129, 0, x_53);
lean_ctor_set(x_129, 1, x_93);
lean_ctor_set(x_129, 2, x_113);
lean_ctor_set(x_129, 3, x_123);
lean_ctor_set(x_129, 4, x_47);
lean_ctor_set(x_129, 5, x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*6, x_52);
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_9);
lean_ctor_set(x_130, 1, x_3);
lean_ctor_set(x_130, 2, x_129);
if (lean_is_scalar(x_8)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_8;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_7);
return x_131;
}
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_24, 0);
lean_inc(x_132);
lean_dec(x_24);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_134; 
lean_dec(x_26);
x_134 = lean_box(0);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_51);
x_135 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_134);
lean_ctor_set(x_135, 4, x_47);
lean_ctor_set(x_135, 5, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*6, x_52);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_9);
lean_ctor_set(x_136, 1, x_3);
lean_ctor_set(x_136, 2, x_135);
if (lean_is_scalar(x_8)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_8;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_7);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_51, 0);
lean_inc(x_138);
lean_dec(x_51);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_134);
lean_ctor_set(x_140, 2, x_134);
lean_ctor_set(x_140, 3, x_134);
lean_ctor_set(x_140, 4, x_47);
lean_ctor_set(x_140, 5, x_139);
lean_ctor_set_uint8(x_140, sizeof(void*)*6, x_52);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_9);
lean_ctor_set(x_141, 1, x_3);
lean_ctor_set(x_141, 2, x_140);
if (lean_is_scalar(x_8)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_8;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_7);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_30, 0);
lean_inc(x_143);
lean_dec(x_30);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_51);
x_145 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_145, 0, x_133);
lean_ctor_set(x_145, 1, x_134);
lean_ctor_set(x_145, 2, x_134);
lean_ctor_set(x_145, 3, x_144);
lean_ctor_set(x_145, 4, x_47);
lean_ctor_set(x_145, 5, x_134);
lean_ctor_set_uint8(x_145, sizeof(void*)*6, x_52);
x_146 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_146, 0, x_9);
lean_ctor_set(x_146, 1, x_3);
lean_ctor_set(x_146, 2, x_145);
if (lean_is_scalar(x_8)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_8;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_7);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_51, 0);
lean_inc(x_148);
lean_dec(x_51);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_150, 0, x_133);
lean_ctor_set(x_150, 1, x_134);
lean_ctor_set(x_150, 2, x_134);
lean_ctor_set(x_150, 3, x_144);
lean_ctor_set(x_150, 4, x_47);
lean_ctor_set(x_150, 5, x_149);
lean_ctor_set_uint8(x_150, sizeof(void*)*6, x_52);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_9);
lean_ctor_set(x_151, 1, x_3);
lean_ctor_set(x_151, 2, x_150);
if (lean_is_scalar(x_8)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_8;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_7);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_28, 0);
lean_inc(x_153);
lean_dec(x_28);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_51);
x_155 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_155, 0, x_133);
lean_ctor_set(x_155, 1, x_134);
lean_ctor_set(x_155, 2, x_154);
lean_ctor_set(x_155, 3, x_134);
lean_ctor_set(x_155, 4, x_47);
lean_ctor_set(x_155, 5, x_134);
lean_ctor_set_uint8(x_155, sizeof(void*)*6, x_52);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_9);
lean_ctor_set(x_156, 1, x_3);
lean_ctor_set(x_156, 2, x_155);
if (lean_is_scalar(x_8)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_8;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_7);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_51, 0);
lean_inc(x_158);
lean_dec(x_51);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_160, 0, x_133);
lean_ctor_set(x_160, 1, x_134);
lean_ctor_set(x_160, 2, x_154);
lean_ctor_set(x_160, 3, x_134);
lean_ctor_set(x_160, 4, x_47);
lean_ctor_set(x_160, 5, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*6, x_52);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_9);
lean_ctor_set(x_161, 1, x_3);
lean_ctor_set(x_161, 2, x_160);
if (lean_is_scalar(x_8)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_8;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_7);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_30, 0);
lean_inc(x_163);
lean_dec(x_30);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_51);
x_165 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_165, 0, x_133);
lean_ctor_set(x_165, 1, x_134);
lean_ctor_set(x_165, 2, x_154);
lean_ctor_set(x_165, 3, x_164);
lean_ctor_set(x_165, 4, x_47);
lean_ctor_set(x_165, 5, x_134);
lean_ctor_set_uint8(x_165, sizeof(void*)*6, x_52);
x_166 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_166, 0, x_9);
lean_ctor_set(x_166, 1, x_3);
lean_ctor_set(x_166, 2, x_165);
if (lean_is_scalar(x_8)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_8;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_7);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_51, 0);
lean_inc(x_168);
lean_dec(x_51);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_170, 0, x_133);
lean_ctor_set(x_170, 1, x_134);
lean_ctor_set(x_170, 2, x_154);
lean_ctor_set(x_170, 3, x_164);
lean_ctor_set(x_170, 4, x_47);
lean_ctor_set(x_170, 5, x_169);
lean_ctor_set_uint8(x_170, sizeof(void*)*6, x_52);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_9);
lean_ctor_set(x_171, 1, x_3);
lean_ctor_set(x_171, 2, x_170);
if (lean_is_scalar(x_8)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_8;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_7);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_26, 0);
lean_inc(x_173);
lean_dec(x_26);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_175; 
lean_dec(x_28);
x_175 = lean_box(0);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_51);
x_176 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_176, 0, x_133);
lean_ctor_set(x_176, 1, x_174);
lean_ctor_set(x_176, 2, x_175);
lean_ctor_set(x_176, 3, x_175);
lean_ctor_set(x_176, 4, x_47);
lean_ctor_set(x_176, 5, x_175);
lean_ctor_set_uint8(x_176, sizeof(void*)*6, x_52);
x_177 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_177, 0, x_9);
lean_ctor_set(x_177, 1, x_3);
lean_ctor_set(x_177, 2, x_176);
if (lean_is_scalar(x_8)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_8;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_7);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_51, 0);
lean_inc(x_179);
lean_dec(x_51);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_181, 0, x_133);
lean_ctor_set(x_181, 1, x_174);
lean_ctor_set(x_181, 2, x_175);
lean_ctor_set(x_181, 3, x_175);
lean_ctor_set(x_181, 4, x_47);
lean_ctor_set(x_181, 5, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*6, x_52);
x_182 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_182, 0, x_9);
lean_ctor_set(x_182, 1, x_3);
lean_ctor_set(x_182, 2, x_181);
if (lean_is_scalar(x_8)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_8;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_7);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_30, 0);
lean_inc(x_184);
lean_dec(x_30);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_51);
x_186 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_186, 0, x_133);
lean_ctor_set(x_186, 1, x_174);
lean_ctor_set(x_186, 2, x_175);
lean_ctor_set(x_186, 3, x_185);
lean_ctor_set(x_186, 4, x_47);
lean_ctor_set(x_186, 5, x_175);
lean_ctor_set_uint8(x_186, sizeof(void*)*6, x_52);
x_187 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_187, 0, x_9);
lean_ctor_set(x_187, 1, x_3);
lean_ctor_set(x_187, 2, x_186);
if (lean_is_scalar(x_8)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_8;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_7);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_51, 0);
lean_inc(x_189);
lean_dec(x_51);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_191, 0, x_133);
lean_ctor_set(x_191, 1, x_174);
lean_ctor_set(x_191, 2, x_175);
lean_ctor_set(x_191, 3, x_185);
lean_ctor_set(x_191, 4, x_47);
lean_ctor_set(x_191, 5, x_190);
lean_ctor_set_uint8(x_191, sizeof(void*)*6, x_52);
x_192 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_192, 0, x_9);
lean_ctor_set(x_192, 1, x_3);
lean_ctor_set(x_192, 2, x_191);
if (lean_is_scalar(x_8)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_8;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_7);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_28, 0);
lean_inc(x_194);
lean_dec(x_28);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_196; 
lean_dec(x_30);
x_196 = lean_box(0);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_51);
x_197 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_197, 0, x_133);
lean_ctor_set(x_197, 1, x_174);
lean_ctor_set(x_197, 2, x_195);
lean_ctor_set(x_197, 3, x_196);
lean_ctor_set(x_197, 4, x_47);
lean_ctor_set(x_197, 5, x_196);
lean_ctor_set_uint8(x_197, sizeof(void*)*6, x_52);
x_198 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_198, 0, x_9);
lean_ctor_set(x_198, 1, x_3);
lean_ctor_set(x_198, 2, x_197);
if (lean_is_scalar(x_8)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_8;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_7);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_51, 0);
lean_inc(x_200);
lean_dec(x_51);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_202, 0, x_133);
lean_ctor_set(x_202, 1, x_174);
lean_ctor_set(x_202, 2, x_195);
lean_ctor_set(x_202, 3, x_196);
lean_ctor_set(x_202, 4, x_47);
lean_ctor_set(x_202, 5, x_201);
lean_ctor_set_uint8(x_202, sizeof(void*)*6, x_52);
x_203 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_203, 0, x_9);
lean_ctor_set(x_203, 1, x_3);
lean_ctor_set(x_203, 2, x_202);
if (lean_is_scalar(x_8)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_8;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_7);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_30, 0);
lean_inc(x_205);
lean_dec(x_30);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_51);
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_208, 0, x_133);
lean_ctor_set(x_208, 1, x_174);
lean_ctor_set(x_208, 2, x_195);
lean_ctor_set(x_208, 3, x_206);
lean_ctor_set(x_208, 4, x_47);
lean_ctor_set(x_208, 5, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*6, x_52);
x_209 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_209, 0, x_9);
lean_ctor_set(x_209, 1, x_3);
lean_ctor_set(x_209, 2, x_208);
if (lean_is_scalar(x_8)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_8;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_7);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_51, 0);
lean_inc(x_211);
lean_dec(x_51);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_213, 0, x_133);
lean_ctor_set(x_213, 1, x_174);
lean_ctor_set(x_213, 2, x_195);
lean_ctor_set(x_213, 3, x_206);
lean_ctor_set(x_213, 4, x_47);
lean_ctor_set(x_213, 5, x_212);
lean_ctor_set_uint8(x_213, sizeof(void*)*6, x_52);
x_214 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_214, 0, x_9);
lean_ctor_set(x_214, 1, x_3);
lean_ctor_set(x_214, 2, x_213);
if (lean_is_scalar(x_8)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_8;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_7);
return x_215;
}
}
}
}
}
}
}
}
}
}
case 1:
{
uint8_t x_227; 
lean_dec(x_3);
x_227 = !lean_is_exclusive(x_5);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_228 = lean_ctor_get(x_5, 0);
lean_dec(x_228);
x_229 = lean_ctor_get(x_6, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_6, 1);
lean_inc(x_230);
lean_dec(x_6);
x_231 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_231, 0, x_229);
x_232 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17;
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_235 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_234, x_230);
lean_dec(x_230);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
x_239 = l_Lean_Json_mkObj(x_238);
x_240 = l_Lean_Json_compress(x_239);
x_241 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_242 = lean_string_append(x_241, x_240);
lean_dec(x_240);
x_243 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_244 = lean_string_append(x_242, x_243);
x_245 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_245);
return x_5;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_246 = lean_ctor_get(x_5, 1);
lean_inc(x_246);
lean_dec(x_5);
x_247 = lean_ctor_get(x_6, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_6, 1);
lean_inc(x_248);
lean_dec(x_6);
x_249 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_249, 0, x_247);
x_250 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17;
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
x_252 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_253 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_252, x_248);
lean_dec(x_248);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_253);
x_255 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
x_257 = l_Lean_Json_mkObj(x_256);
x_258 = l_Lean_Json_compress(x_257);
x_259 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_260 = lean_string_append(x_259, x_258);
lean_dec(x_258);
x_261 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_262 = lean_string_append(x_260, x_261);
x_263 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_263, 0, x_262);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_246);
return x_264;
}
}
case 2:
{
uint8_t x_265; 
lean_dec(x_3);
x_265 = !lean_is_exclusive(x_5);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_266 = lean_ctor_get(x_5, 0);
lean_dec(x_266);
x_267 = lean_ctor_get(x_6, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_6, 1);
lean_inc(x_268);
lean_dec(x_6);
x_269 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20;
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
x_271 = lean_box(0);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
switch (lean_obj_tag(x_267)) {
case 0:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_273 = lean_ctor_get(x_267, 0);
lean_inc(x_273);
lean_dec(x_267);
x_274 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_272);
x_278 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
x_280 = l_Lean_Json_mkObj(x_279);
x_281 = l_Lean_Json_compress(x_280);
x_282 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_283 = lean_string_append(x_282, x_281);
lean_dec(x_281);
x_284 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_285 = lean_string_append(x_283, x_284);
x_286 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_286);
return x_5;
}
case 1:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_287 = lean_ctor_get(x_267, 0);
lean_inc(x_287);
lean_dec(x_267);
x_288 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_289 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_272);
x_292 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = l_Lean_Json_mkObj(x_293);
x_295 = l_Lean_Json_compress(x_294);
x_296 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_297 = lean_string_append(x_296, x_295);
lean_dec(x_295);
x_298 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_299 = lean_string_append(x_297, x_298);
x_300 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_300);
return x_5;
}
default: 
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_301 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22;
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_272);
x_303 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_302);
x_305 = l_Lean_Json_mkObj(x_304);
x_306 = l_Lean_Json_compress(x_305);
x_307 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_308 = lean_string_append(x_307, x_306);
lean_dec(x_306);
x_309 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_310 = lean_string_append(x_308, x_309);
x_311 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_311);
return x_5;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_312 = lean_ctor_get(x_5, 1);
lean_inc(x_312);
lean_dec(x_5);
x_313 = lean_ctor_get(x_6, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_6, 1);
lean_inc(x_314);
lean_dec(x_6);
x_315 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20;
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_314);
x_317 = lean_box(0);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
switch (lean_obj_tag(x_313)) {
case 0:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_319 = lean_ctor_get(x_313, 0);
lean_inc(x_319);
lean_dec(x_313);
x_320 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_320, 0, x_319);
x_321 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_320);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_318);
x_324 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
x_326 = l_Lean_Json_mkObj(x_325);
x_327 = l_Lean_Json_compress(x_326);
x_328 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_329 = lean_string_append(x_328, x_327);
lean_dec(x_327);
x_330 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_331 = lean_string_append(x_329, x_330);
x_332 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_332, 0, x_331);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_312);
return x_333;
}
case 1:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_334 = lean_ctor_get(x_313, 0);
lean_inc(x_334);
lean_dec(x_313);
x_335 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_335, 0, x_334);
x_336 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_335);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_318);
x_339 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
x_341 = l_Lean_Json_mkObj(x_340);
x_342 = l_Lean_Json_compress(x_341);
x_343 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_344 = lean_string_append(x_343, x_342);
lean_dec(x_342);
x_345 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_346 = lean_string_append(x_344, x_345);
x_347 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_347, 0, x_346);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_312);
return x_348;
}
default: 
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_349 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22;
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_318);
x_351 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_350);
x_353 = l_Lean_Json_mkObj(x_352);
x_354 = l_Lean_Json_compress(x_353);
x_355 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_356 = lean_string_append(x_355, x_354);
lean_dec(x_354);
x_357 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_358 = lean_string_append(x_356, x_357);
x_359 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_359, 0, x_358);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_312);
return x_360;
}
}
}
}
default: 
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_3);
x_361 = lean_ctor_get(x_5, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_362 = x_5;
} else {
 lean_dec_ref(x_5);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_6, 0);
lean_inc(x_363);
x_364 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_365 = lean_ctor_get(x_6, 1);
lean_inc(x_365);
x_366 = lean_ctor_get(x_6, 2);
lean_inc(x_366);
lean_dec(x_6);
x_367 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_367, 0, x_365);
x_368 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23;
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_367);
x_370 = lean_box(0);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_372 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24;
x_373 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_372, x_366);
lean_dec(x_366);
switch (lean_obj_tag(x_363)) {
case 0:
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_363, 0);
lean_inc(x_411);
lean_dec(x_363);
x_412 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_412, 0, x_411);
x_374 = x_412;
goto block_410;
}
case 1:
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_363, 0);
lean_inc(x_413);
lean_dec(x_363);
x_414 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_414, 0, x_413);
x_374 = x_414;
goto block_410;
}
default: 
{
lean_object* x_415; 
x_415 = lean_box(0);
x_374 = x_415;
goto block_410;
}
}
block_410:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
switch (x_364) {
case 0:
{
lean_object* x_398; 
x_398 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30;
x_377 = x_398;
goto block_397;
}
case 1:
{
lean_object* x_399; 
x_399 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34;
x_377 = x_399;
goto block_397;
}
case 2:
{
lean_object* x_400; 
x_400 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38;
x_377 = x_400;
goto block_397;
}
case 3:
{
lean_object* x_401; 
x_401 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42;
x_377 = x_401;
goto block_397;
}
case 4:
{
lean_object* x_402; 
x_402 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46;
x_377 = x_402;
goto block_397;
}
case 5:
{
lean_object* x_403; 
x_403 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50;
x_377 = x_403;
goto block_397;
}
case 6:
{
lean_object* x_404; 
x_404 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54;
x_377 = x_404;
goto block_397;
}
case 7:
{
lean_object* x_405; 
x_405 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58;
x_377 = x_405;
goto block_397;
}
case 8:
{
lean_object* x_406; 
x_406 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62;
x_377 = x_406;
goto block_397;
}
case 9:
{
lean_object* x_407; 
x_407 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__66;
x_377 = x_407;
goto block_397;
}
case 10:
{
lean_object* x_408; 
x_408 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__70;
x_377 = x_408;
goto block_397;
}
default: 
{
lean_object* x_409; 
x_409 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__74;
x_377 = x_409;
goto block_397;
}
}
block_397:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_378 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25;
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_377);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_371);
x_381 = l_List_appendTR___rarg(x_380, x_373);
x_382 = l_Lean_Json_mkObj(x_381);
x_383 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26;
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_370);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_376);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_386);
x_389 = l_Lean_Json_mkObj(x_388);
x_390 = l_Lean_Json_compress(x_389);
x_391 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19;
x_392 = lean_string_append(x_391, x_390);
lean_dec(x_390);
x_393 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_394 = lean_string_append(x_392, x_393);
x_395 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_395, 0, x_394);
if (lean_is_scalar(x_362)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_362;
 lean_ctor_set_tag(x_396, 1);
}
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_361);
return x_396;
}
}
}
}
}
else
{
uint8_t x_416; 
lean_dec(x_3);
x_416 = !lean_is_exclusive(x_5);
if (x_416 == 0)
{
return x_5;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_5, 0);
x_418 = lean_ctor_get(x_5, 1);
lean_inc(x_418);
lean_inc(x_417);
lean_dec(x_5);
x_419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_418);
return x_419;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Cannot read LSP request: ", 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2(x_1, x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_io_error_to_string(x_9);
x_11 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_io_error_to_string(x_16);
x_19 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_io_error_to_string(x_33);
x_36 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expected JSON-RPC notification, got: '", 38);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readMessage(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_18 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_17, x_11);
lean_dec(x_11);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
x_24 = l_List_appendTR___rarg(x_23, x_18);
x_25 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Json_mkObj(x_26);
x_28 = l_Lean_Json_compress(x_27);
x_29 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_33);
return x_5;
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_9, 0);
lean_inc(x_34);
lean_dec(x_9);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_16);
x_39 = l_List_appendTR___rarg(x_38, x_18);
x_40 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Json_mkObj(x_41);
x_43 = l_Lean_Json_compress(x_42);
x_44 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_48);
return x_5;
}
default: 
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_16);
x_51 = l_List_appendTR___rarg(x_50, x_18);
x_52 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Json_mkObj(x_53);
x_55 = l_Lean_Json_compress(x_54);
x_56 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_60);
return x_5;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
lean_dec(x_5);
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_6, 2);
lean_inc(x_64);
lean_dec(x_6);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18;
x_71 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_70, x_64);
lean_dec(x_64);
switch (lean_obj_tag(x_62)) {
case 0:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
lean_dec(x_62);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
x_77 = l_List_appendTR___rarg(x_76, x_71);
x_78 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Json_mkObj(x_79);
x_81 = l_Lean_Json_compress(x_80);
x_82 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_84 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_61);
return x_87;
}
case 1:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_88 = lean_ctor_get(x_62, 0);
lean_inc(x_88);
lean_dec(x_62);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_69);
x_93 = l_List_appendTR___rarg(x_92, x_71);
x_94 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Json_mkObj(x_95);
x_97 = l_Lean_Json_compress(x_96);
x_98 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_99 = lean_string_append(x_98, x_97);
lean_dec(x_97);
x_100 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_61);
return x_103;
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_104 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_69);
x_106 = l_List_appendTR___rarg(x_105, x_71);
x_107 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Json_mkObj(x_108);
x_110 = l_Lean_Json_compress(x_109);
x_111 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_112 = lean_string_append(x_111, x_110);
lean_dec(x_110);
x_113 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_114 = lean_string_append(x_112, x_113);
x_115 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_61);
return x_116;
}
}
}
}
case 1:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_5, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_118 = x_5;
} else {
 lean_dec_ref(x_5);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_6, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_6, 1);
lean_inc(x_120);
lean_dec(x_6);
x_121 = lean_string_dec_eq(x_119, x_3);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_120);
x_122 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1;
x_123 = lean_string_append(x_122, x_3);
lean_dec(x_3);
x_124 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_string_append(x_125, x_119);
lean_dec(x_119);
x_127 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_128 = lean_string_append(x_126, x_127);
x_129 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_129, 0, x_128);
if (lean_is_scalar(x_118)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_118;
 lean_ctor_set_tag(x_130, 1);
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_117);
return x_130;
}
else
{
lean_object* x_131; 
lean_dec(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_151; 
x_151 = lean_box(0);
x_131 = x_151;
goto block_150;
}
else
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_120, 0);
lean_inc(x_152);
lean_dec(x_120);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_131 = x_154;
goto block_150;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_131 = x_156;
goto block_150;
}
}
block_150:
{
lean_object* x_132; 
x_132 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_202_(x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
x_134 = l_Lean_Json_compress(x_131);
x_135 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8;
x_136 = lean_string_append(x_135, x_134);
lean_dec(x_134);
x_137 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9;
x_138 = lean_string_append(x_136, x_137);
x_139 = lean_string_append(x_138, x_3);
lean_dec(x_3);
x_140 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10;
x_141 = lean_string_append(x_139, x_140);
x_142 = lean_string_append(x_141, x_133);
lean_dec(x_133);
x_143 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_144 = lean_string_append(x_142, x_143);
x_145 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_145, 0, x_144);
if (lean_is_scalar(x_118)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_118;
 lean_ctor_set_tag(x_146, 1);
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_117);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_131);
x_147 = lean_ctor_get(x_132, 0);
lean_inc(x_147);
lean_dec(x_132);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_3);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_118)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_118;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_117);
return x_149;
}
}
}
}
case 2:
{
uint8_t x_157; 
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_5);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_5, 0);
lean_dec(x_158);
x_159 = lean_ctor_get(x_6, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_6, 1);
lean_inc(x_160);
lean_dec(x_6);
x_161 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
switch (lean_obj_tag(x_159)) {
case 0:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_165 = lean_ctor_get(x_159, 0);
lean_inc(x_165);
lean_dec(x_159);
x_166 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_167 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_164);
x_170 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = l_Lean_Json_mkObj(x_171);
x_173 = l_Lean_Json_compress(x_172);
x_174 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_175 = lean_string_append(x_174, x_173);
lean_dec(x_173);
x_176 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_177 = lean_string_append(x_175, x_176);
x_178 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_178);
return x_5;
}
case 1:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_179 = lean_ctor_get(x_159, 0);
lean_inc(x_179);
lean_dec(x_159);
x_180 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_164);
x_184 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = l_Lean_Json_mkObj(x_185);
x_187 = l_Lean_Json_compress(x_186);
x_188 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_192);
return x_5;
}
default: 
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_193 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22;
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_164);
x_195 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = l_Lean_Json_mkObj(x_196);
x_198 = l_Lean_Json_compress(x_197);
x_199 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_200 = lean_string_append(x_199, x_198);
lean_dec(x_198);
x_201 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_202 = lean_string_append(x_200, x_201);
x_203 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_203);
return x_5;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_204 = lean_ctor_get(x_5, 1);
lean_inc(x_204);
lean_dec(x_5);
x_205 = lean_ctor_get(x_6, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_6, 1);
lean_inc(x_206);
lean_dec(x_6);
x_207 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20;
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
switch (lean_obj_tag(x_205)) {
case 0:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_211 = lean_ctor_get(x_205, 0);
lean_inc(x_211);
lean_dec(x_205);
x_212 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_212, 0, x_211);
x_213 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_210);
x_216 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
x_218 = l_Lean_Json_mkObj(x_217);
x_219 = l_Lean_Json_compress(x_218);
x_220 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_221 = lean_string_append(x_220, x_219);
lean_dec(x_219);
x_222 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_223 = lean_string_append(x_221, x_222);
x_224 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_204);
return x_225;
}
case 1:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_226 = lean_ctor_get(x_205, 0);
lean_inc(x_226);
lean_dec(x_205);
x_227 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_210);
x_231 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = l_Lean_Json_mkObj(x_232);
x_234 = l_Lean_Json_compress(x_233);
x_235 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_236 = lean_string_append(x_235, x_234);
lean_dec(x_234);
x_237 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_238 = lean_string_append(x_236, x_237);
x_239 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_204);
return x_240;
}
default: 
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_241 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22;
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_210);
x_243 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
x_245 = l_Lean_Json_mkObj(x_244);
x_246 = l_Lean_Json_compress(x_245);
x_247 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_248 = lean_string_append(x_247, x_246);
lean_dec(x_246);
x_249 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_250 = lean_string_append(x_248, x_249);
x_251 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_251, 0, x_250);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_204);
return x_252;
}
}
}
}
default: 
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_3);
x_253 = lean_ctor_get(x_5, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_254 = x_5;
} else {
 lean_dec_ref(x_5);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_6, 0);
lean_inc(x_255);
x_256 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_257 = lean_ctor_get(x_6, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_6, 2);
lean_inc(x_258);
lean_dec(x_6);
x_259 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_259, 0, x_257);
x_260 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23;
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
x_262 = lean_box(0);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24;
x_265 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_264, x_258);
lean_dec(x_258);
switch (lean_obj_tag(x_255)) {
case 0:
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_255, 0);
lean_inc(x_303);
lean_dec(x_255);
x_304 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_304, 0, x_303);
x_266 = x_304;
goto block_302;
}
case 1:
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_255, 0);
lean_inc(x_305);
lean_dec(x_255);
x_306 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_306, 0, x_305);
x_266 = x_306;
goto block_302;
}
default: 
{
lean_object* x_307; 
x_307 = lean_box(0);
x_266 = x_307;
goto block_302;
}
}
block_302:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21;
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
switch (x_256) {
case 0:
{
lean_object* x_290; 
x_290 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30;
x_269 = x_290;
goto block_289;
}
case 1:
{
lean_object* x_291; 
x_291 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34;
x_269 = x_291;
goto block_289;
}
case 2:
{
lean_object* x_292; 
x_292 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38;
x_269 = x_292;
goto block_289;
}
case 3:
{
lean_object* x_293; 
x_293 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42;
x_269 = x_293;
goto block_289;
}
case 4:
{
lean_object* x_294; 
x_294 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46;
x_269 = x_294;
goto block_289;
}
case 5:
{
lean_object* x_295; 
x_295 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50;
x_269 = x_295;
goto block_289;
}
case 6:
{
lean_object* x_296; 
x_296 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54;
x_269 = x_296;
goto block_289;
}
case 7:
{
lean_object* x_297; 
x_297 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58;
x_269 = x_297;
goto block_289;
}
case 8:
{
lean_object* x_298; 
x_298 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62;
x_269 = x_298;
goto block_289;
}
case 9:
{
lean_object* x_299; 
x_299 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__66;
x_269 = x_299;
goto block_289;
}
case 10:
{
lean_object* x_300; 
x_300 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__70;
x_269 = x_300;
goto block_289;
}
default: 
{
lean_object* x_301; 
x_301 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__74;
x_269 = x_301;
goto block_289;
}
}
block_289:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_270 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25;
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_263);
x_273 = l_List_appendTR___rarg(x_272, x_265);
x_274 = l_Lean_Json_mkObj(x_273);
x_275 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26;
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_262);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_268);
lean_ctor_set(x_278, 1, x_277);
x_279 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16;
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
x_281 = l_Lean_Json_mkObj(x_280);
x_282 = l_Lean_Json_compress(x_281);
x_283 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1;
x_284 = lean_string_append(x_283, x_282);
lean_dec(x_282);
x_285 = l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2;
x_286 = lean_string_append(x_284, x_285);
x_287 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_287, 0, x_286);
if (lean_is_scalar(x_254)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_254;
 lean_ctor_set_tag(x_288, 1);
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_253);
return x_288;
}
}
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_3);
x_308 = !lean_is_exclusive(x_5);
if (x_308 == 0)
{
return x_5;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_5, 0);
x_310 = lean_ctor_get(x_5, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_5);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
}
static lean_object* _init_l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Cannot read LSP notification: ", 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4(x_1, x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_io_error_to_string(x_9);
x_11 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_io_error_to_string(x_16);
x_19 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_io_error_to_string(x_33);
x_36 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at_Lean_Server_FileWorker_initAndRunWorker___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_io_error_to_string(x_1);
x_4 = 10;
x_5 = lean_string_push(x_3, x_4);
x_6 = l_IO_eprint___at_IO_eprintln___spec__1(x_5, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fwIn.txt", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fwOut.txt", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initialize", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("textDocument/didOpen", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__5() {
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
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("] ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_initAndRunWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = l_Lean_Server_FileWorker_initAndRunWorker___closed__1;
x_7 = 0;
x_8 = l_Lean_Server_maybeTee(x_6, x_7, x_1, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Server_FileWorker_initAndRunWorker___closed__2;
x_12 = 1;
x_13 = l_Lean_Server_maybeTee(x_11, x_12, x_2, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Server_FileWorker_initAndRunWorker___closed__3;
lean_inc(x_9);
x_17 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1(x_9, x_16, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Server_FileWorker_initAndRunWorker___closed__4;
lean_inc(x_9);
x_21 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3(x_9, x_20, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 3);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_FileMap_ofString(x_27);
lean_inc(x_25);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
x_58 = l_Lean_Server_FileWorker_initAndRunWorker___closed__6;
x_59 = lean_string_append(x_58, x_25);
lean_dec(x_25);
x_60 = l_Lean_Server_FileWorker_initAndRunWorker___closed__7;
x_61 = lean_string_append(x_59, x_60);
x_62 = l_IO_FS_Stream_withPrefix(x_3, x_61);
lean_inc(x_62);
x_63 = lean_get_set_stderr(x_62, x_24);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get(x_18, 2);
lean_inc(x_65);
lean_dec(x_18);
lean_inc(x_14);
lean_inc(x_29);
x_66 = l_Lean_Server_FileWorker_initializeWorker(x_29, x_9, x_14, x_62, x_65, x_4, x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_st_mk_ref(x_70, x_68);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_72);
x_74 = l_Lean_Server_FileWorker_mainLoop(x_69, x_72, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_29);
lean_dec(x_14);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_st_ref_get(x_72, x_75);
lean_dec(x_72);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2;
lean_ctor_set(x_76, 0, x_79);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2;
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_72);
x_83 = lean_ctor_get(x_74, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_dec(x_74);
x_30 = x_83;
x_31 = x_84;
goto block_57;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_66, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_66, 1);
lean_inc(x_86);
lean_dec(x_66);
x_30 = x_85;
x_31 = x_86;
goto block_57;
}
block_57:
{
lean_object* x_32; 
lean_inc(x_30);
x_32 = l_IO_eprintln___at_Lean_Server_FileWorker_initAndRunWorker___spec__5(x_30, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = lean_io_error_to_string(x_30);
x_36 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3;
x_37 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4;
x_38 = l_Lean_Server_FileWorker_initAndRunWorker___closed__5;
x_39 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_34);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_34);
lean_ctor_set(x_39, 7, x_34);
lean_ctor_set(x_39, 8, x_34);
x_40 = l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1;
x_41 = lean_array_push(x_40, x_39);
x_42 = l_Lean_Server_publishDiagnostics(x_29, x_41, x_14, x_33);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1;
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_14);
x_53 = !lean_is_exclusive(x_32);
if (x_53 == 0)
{
return x_32;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_32, 0);
x_55 = lean_ctor_get(x_32, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_32);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_87 = !lean_is_exclusive(x_21);
if (x_87 == 0)
{
return x_21;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_21, 0);
x_89 = lean_ctor_get(x_21, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_21);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_17);
if (x_91 == 0)
{
return x_17;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_17, 0);
x_93 = lean_ctor_get(x_17, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_17);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_13);
if (x_95 == 0)
{
return x_13;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_13, 0);
x_97 = lean_ctor_get(x_13, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_13);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_8);
if (x_99 == 0)
{
return x_8;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_8, 0);
x_101 = lean_ctor_get(x_8, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_8);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_workerMain___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("worker initialization error: ", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_workerMain___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_server_worker_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_31; 
x_3 = lean_get_stdin(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_get_stdout(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_get_stderr(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
lean_inc(x_7);
x_31 = l_Lean_Server_FileWorker_initAndRunWorker(x_4, x_7, x_10, x_1, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_apply_1(x_34, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_10, 0);
lean_inc(x_37);
x_38 = lean_apply_1(x_37, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_unbox_uint32(x_32);
lean_dec(x_32);
x_41 = lean_uint32_to_uint8(x_40);
x_42 = lean_io_exit(x_41, x_39);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_12 = x_47;
x_13 = x_48;
goto block_30;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_32);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_12 = x_49;
x_13 = x_50;
goto block_30;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_32);
x_51 = lean_ctor_get(x_35, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_dec(x_35);
x_12 = x_51;
x_13 = x_52;
goto block_30;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_7);
x_53 = lean_ctor_get(x_31, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_31, 1);
lean_inc(x_54);
lean_dec(x_31);
x_12 = x_53;
x_13 = x_54;
goto block_30;
}
block_30:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_io_error_to_string(x_12);
x_15 = l_Lean_Server_FileWorker_workerMain___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_IO_FS_Stream_putStrLn(x_10, x_18, x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = l_Lean_Server_FileWorker_workerMain___boxed__const__1;
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Server_FileWorker_workerMain___boxed__const__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_FromToJson(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Paths(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LoadDynlib(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Snapshots(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_References(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_FileWorker_RequestHandling(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_FileWorker_WidgetRequests(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_FromToJson(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Paths(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LoadDynlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Snapshots(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_AsyncList(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_References(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_RequestHandling(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileWorker_WidgetRequests(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveDiagnostic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__1 = _init_l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__1();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__1);
l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2 = _init_l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2();
lean_mark_persistent(l_Lean_Json_toStructured_x3f___at___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfo___spec__3___closed__2);
l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate___closed__1 = _init_l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate___closed__1();
lean_mark_persistent(l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoUpdate___closed__1);
l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal___closed__1 = _init_l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal___closed__1();
lean_mark_persistent(l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_publishIleanInfoFinal___closed__1);
l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1 = _init_l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Server_FileWorker_0__Lean_Server_FileWorker_nextCmdSnap___lambda__1___closed__1);
l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__1);
l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__2);
l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__3);
l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__4);
l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath_processStderr___closed__5);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__1);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__2);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__3);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__4);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__5);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__6);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__7);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__8);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__9);
l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10 = _init_l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10();
lean_mark_persistent(l_Lean_Server_FileWorker_lakeSetupSearchPath___closed__10);
l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__1 = _init_l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__1);
l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__2 = _init_l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__2);
l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__3 = _init_l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__3();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Server_FileWorker_compileHeader___spec__1___closed__3);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__1);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__2);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__3);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__4);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__5);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__6);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__7);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__8 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__8);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__9 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__9);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__10 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__10);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__11 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__11);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__12 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__12);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__13 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__13);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__14 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__14);
l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__15 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__1___closed__15);
l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__1);
l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__2 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__2);
l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__3 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__3);
l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__4 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__3___closed__4);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__1);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__2);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__3);
l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4 = _init_l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___lambda__5___closed__4);
l_Lean_Server_FileWorker_compileHeader___closed__1 = _init_l_Lean_Server_FileWorker_compileHeader___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_compileHeader___closed__1);
l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__1 = _init_l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__1);
l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__2 = _init_l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__2);
l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__3 = _init_l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__3);
l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__4 = _init_l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_updateDocument___lambda__6___closed__4);
l_Lean_Server_FileWorker_updateDocument___closed__1 = _init_l_Lean_Server_FileWorker_updateDocument___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_updateDocument___closed__1);
l_Lean_Server_FileWorker_handleDidChange___closed__1 = _init_l_Lean_Server_FileWorker_handleDidChange___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleDidChange___closed__1);
l_Lean_Server_FileWorker_handleDidChange___closed__2 = _init_l_Lean_Server_FileWorker_handleDidChange___closed__2();
l_Lean_Server_FileWorker_handleDidChange___closed__3 = _init_l_Lean_Server_FileWorker_handleDidChange___closed__3();
l_Lean_Server_FileWorker_handleDidChange___closed__4 = _init_l_Lean_Server_FileWorker_handleDidChange___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_handleDidChange___closed__4);
l_Lean_Server_FileWorker_handleDidChange___closed__5 = _init_l_Lean_Server_FileWorker_handleDidChange___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_handleDidChange___closed__5);
l_Lean_Server_FileWorker_parseParams___rarg___closed__1 = _init_l_Lean_Server_FileWorker_parseParams___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_parseParams___rarg___closed__1);
l_Lean_Server_FileWorker_parseParams___rarg___closed__2 = _init_l_Lean_Server_FileWorker_parseParams___rarg___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_parseParams___rarg___closed__2);
l_Lean_Server_FileWorker_handleNotification___closed__1 = _init_l_Lean_Server_FileWorker_handleNotification___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleNotification___closed__1);
l_Lean_Server_FileWorker_handleNotification___closed__2 = _init_l_Lean_Server_FileWorker_handleNotification___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_handleNotification___closed__2);
l_Lean_Server_FileWorker_handleNotification___closed__3 = _init_l_Lean_Server_FileWorker_handleNotification___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_handleNotification___closed__3);
l_Lean_Server_FileWorker_handleNotification___closed__4 = _init_l_Lean_Server_FileWorker_handleNotification___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_handleNotification___closed__4);
l_Lean_Server_FileWorker_handleNotification___closed__5 = _init_l_Lean_Server_FileWorker_handleNotification___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_handleNotification___closed__5);
l_Lean_Server_FileWorker_handleRequest___closed__1 = _init_l_Lean_Server_FileWorker_handleRequest___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_handleRequest___closed__1);
l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1 = _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__1);
l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2 = _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__2);
l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3 = _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__3);
l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4 = _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__4);
l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5 = _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__5);
l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6 = _init_l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6();
lean_mark_persistent(l_Lean_RBNode_foldM___at_Lean_Server_FileWorker_mainLoop___spec__1___closed__6);
l_Lean_Server_FileWorker_mainLoop___closed__1 = _init_l_Lean_Server_FileWorker_mainLoop___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_mainLoop___closed__1);
l_Lean_Server_FileWorker_mainLoop___closed__2 = _init_l_Lean_Server_FileWorker_mainLoop___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_mainLoop___closed__2);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__1);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__2);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__3);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__4);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__5);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__6);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__7);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__8);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__9);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__10);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__11);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__12);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__13);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__14);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__15);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__16);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__17);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__18);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__19);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__20);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__21);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__22);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__23);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__24);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__25);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__26);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__27);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__28);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__29);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__30);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__31);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__32);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__33);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__34);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__35);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__36);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__37);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__38);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__39);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__40);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__41);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__42);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__43);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__44);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__45);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__46);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__47);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__48);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__49);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__50);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__51);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__52);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__53);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__54);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__55);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__56);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__57);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__58);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__59);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__60);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__61);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__62);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__63);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__64 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__64();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__64);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__65 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__65();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__65);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__66 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__66();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__66);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__67 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__67();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__67);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__68 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__68();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__68);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__69 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__69();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__69);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__70 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__70();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__70);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__71 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__71();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__71);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__72 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__72();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__72);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__73 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__73();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__73);
l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__74 = _init_l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__74();
lean_mark_persistent(l_IO_FS_Stream_readRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__2___closed__74);
l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1 = _init_l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__1___closed__1);
l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1 = _init_l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__4___closed__1);
l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1 = _init_l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1();
lean_mark_persistent(l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_FileWorker_initAndRunWorker___spec__3___closed__1);
l_Lean_Server_FileWorker_initAndRunWorker___closed__1 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__1);
l_Lean_Server_FileWorker_initAndRunWorker___closed__2 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__2);
l_Lean_Server_FileWorker_initAndRunWorker___closed__3 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__3);
l_Lean_Server_FileWorker_initAndRunWorker___closed__4 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__4);
l_Lean_Server_FileWorker_initAndRunWorker___closed__5 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__5);
l_Lean_Server_FileWorker_initAndRunWorker___closed__6 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__6);
l_Lean_Server_FileWorker_initAndRunWorker___closed__7 = _init_l_Lean_Server_FileWorker_initAndRunWorker___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___closed__7);
l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1 = _init_l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__1);
l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2 = _init_l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2();
lean_mark_persistent(l_Lean_Server_FileWorker_initAndRunWorker___boxed__const__2);
l_Lean_Server_FileWorker_workerMain___closed__1 = _init_l_Lean_Server_FileWorker_workerMain___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_workerMain___closed__1);
l_Lean_Server_FileWorker_workerMain___boxed__const__1 = _init_l_Lean_Server_FileWorker_workerMain___boxed__const__1();
lean_mark_persistent(l_Lean_Server_FileWorker_workerMain___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
