import Research.TaskU.H5.TraceWords
import Research.TaskU.H5.Profile

namespace TaskU.H5.TraceWords
noncomputable section

/-- Cyclotomic coordinates of the five-dimensional determinant at ζ. -/
def nonlinear (f : H → ℤ) : Cyc5.V := profile (counts (weight f) phase)

end
end TaskU.H5.TraceWords
