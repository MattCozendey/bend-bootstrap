# compiler: layer B6, the proofs of am/spec.bend
# ==============================================
#
# One def per law of am/spec.bend. am.ok splits by AM.move's cases, one
# helper per move; each is a short term argument from Eval's facts (a value
# has no step; a focus with no step that is no value makes its frames' term
# so: eval_facts.bend at 4ebef88, to port), canon/spec.bend's laws, and
# am.walk_eval for the calls.

import Base
import ../../../Book/impl.bend as Bk
import ../../../Eval/impl.bend as El
import ../../../Program/impl.bend as Pg
import ../canon/spec.bend as C
import ./spec.bend as A

def A.am.ok(ds, vb, s, ok):
  ?TODO

def A.am.walk_eval(ds, t, e, xs):
  ?TODO
