import QRH.S7_1_Core
import QRH.S7_1_Main
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Algebra.Group.Indicator

open scoped MeasureTheory
open Real

noncomputable section

#check MeasureTheory.AEMeasurable.aestronglyMeasurable
#check MeasureTheory.Measurable.aemeasurable
#check aestronglyMeasurable_iff_aemeasurable
#check MeasureTheory.aestronglyMeasurable
#check MeasureTheory.IntegrableOn.congr_fun
#check MeasureTheory.Integrable.const_mul
#check MeasureTheory.integral_mono_ae
#check Set.indicator_of_mem
#check MeasureTheory.integrableOn_iff_integrable_of_support_subset
#check MeasureTheory.Integrable.aestronglyMeasurable
#check MeasureTheory.AEStronglyMeasurable.norm
#check MeasureTheory.integral_add
#check MeasureTheory.Integrable.add

end
