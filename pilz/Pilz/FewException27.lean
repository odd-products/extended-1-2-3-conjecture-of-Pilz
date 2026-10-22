import Pilz.FewExceptions
import Pilz.CompatibilitySlices
import Pilz.SmallBTable

/-! The length-27 exception, joined to the independently proved slice budget. -/

noncomputable section

namespace Pilz

theorem four_term_at_twenty_seven_of_core
    (hcore : 7 ≤ distance (smoothInterval (primesUpTo 5) 27))
    (D : Poly) (hw : weight D = 4) : 36 ≤ weight (interval 27 * D) :=
  four_term_at_twenty_seven_of_core_compatibility hcore
    four_term_interval_compatibility D hw

/-- The paper's strengthened four-term estimate at length 27. -/
theorem four_term_at_twenty_seven (D : Poly) (hw : weight D = 4) :
    36 ≤ weight (interval 27 * D) :=
  four_term_at_twenty_seven_of_core smallB_twentyseven_distance_seven D hw

end Pilz
