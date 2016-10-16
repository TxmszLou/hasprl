module Judgment where

import Refine.Context
import Compute.TermDeBruijn

-- the refinement judgment
-- H >> e = e : A
-- H is the refinement context, e is the term to be refined to type A

-- here c is the context
data Judgment c = Judgment c Tm Tm
                deriving (Eq,Show)
