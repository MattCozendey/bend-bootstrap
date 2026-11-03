# compiler: layer B, the start, as Inv (U8)
# =========================================
#
# input.post and input.done of move_kit.bend: start_input.bend's In.input.post and In.input.done
# (PostB form), then In.PostIn gives InvIn, with Acc (the cache and the start term's nodes).
# Filled by U8; U0 left each as ?TODO.

import Base
import ./move_kit.bend as K

def K.input.post(f, p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ?TODO

def K.input.done(p, ds, i, m, k, len, pg, lim, first, rd, small, s):
  ?TODO
