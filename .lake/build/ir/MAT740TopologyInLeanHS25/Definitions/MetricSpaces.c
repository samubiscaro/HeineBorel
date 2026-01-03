// Lean compiler output
// Module: MAT740TopologyInLeanHS25.Definitions.MetricSpaces
// Imports: Init Mathlib.Tactic MAT740TopologyInLeanHS25.Definitions.TopologicalSpaces MAT740TopologyInLeanHS25.Definitions.Bases
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
LEAN_EXPORT lean_object* l_metricTopology(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_metricBasis___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_metricTopology___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_metricBasis(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_metricBasis(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_metricBasis___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_metricBasis(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_metricTopology(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_metricTopology___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_metricTopology(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_MAT740TopologyInLeanHS25_Definitions_TopologicalSpaces(uint8_t builtin, lean_object*);
lean_object* initialize_MAT740TopologyInLeanHS25_Definitions_Bases(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MAT740TopologyInLeanHS25_Definitions_MetricSpaces(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MAT740TopologyInLeanHS25_Definitions_TopologicalSpaces(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MAT740TopologyInLeanHS25_Definitions_Bases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
