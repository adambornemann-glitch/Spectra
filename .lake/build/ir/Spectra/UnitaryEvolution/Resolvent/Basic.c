// Lean compiler output
// Module: Spectra.UnitaryEvolution.Resolvent.Basic
// Imports: public import Init public meta import Init public import Spectra.UnitaryEvolution.BochnerIntegration.Resolvent
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
LEAN_EXPORT lean_object* lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___lam__0___boxed(lean_object*);
static const lean_closure_object lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___closed__0 = (const lean_object*)&lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___closed__0_value;
LEAN_EXPORT const lean_object* lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis = (const lean_object*)&lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___closed__0_value;
LEAN_EXPORT const lean_object* lp_Spectra_QuantumMechanics_Resolvent_instCoeLowerHalfPlaneOffRealAxis = (const lean_object*)&lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___closed__0_value;
LEAN_EXPORT lean_object* lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___lam__0(lean_object* v_z_1_){
_start:
{
lean_inc_ref(v_z_1_);
return v_z_1_;
}
}
LEAN_EXPORT lean_object* lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___lam__0___boxed(lean_object* v_z_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = lp_Spectra_QuantumMechanics_Resolvent_instCoeUpperHalfPlaneOffRealAxis___lam__0(v_z_2_);
lean_dec_ref(v_z_2_);
return v_res_3_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Spectra_Spectra_UnitaryEvolution_BochnerIntegration_Resolvent(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Spectra_Spectra_UnitaryEvolution_Resolvent_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Spectra_Spectra_UnitaryEvolution_BochnerIntegration_Resolvent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
