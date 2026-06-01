// Lean compiler output
// Module: Spectra.UnitaryEvolution.Yosida.ExpBounded.Basic
// Imports: public import Init public meta import Init public import Spectra.UnitaryEvolution.Yosida.Convergence.Approximants
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Spectra_Spectra_UnitaryEvolution_Yosida_Convergence_Approximants(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Spectra_Spectra_UnitaryEvolution_Yosida_ExpBounded_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Spectra_Spectra_UnitaryEvolution_Yosida_Convergence_Approximants(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
