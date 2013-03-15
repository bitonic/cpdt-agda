-- Reformulation in Agda of the examples given in CPDT.

-- This is for personal edification and to see if and how things are more
-- difficult in Agda.

-- In any case it is not a fair comparison since I am keeping the translation
-- quite direct, and since CPDT is quite tactic heavy restructuring the programs
-- more heavily might lead to benefits in Agda.

module README where

import StackMachine
import InductiveTypes
import Predicates
-- import Coinductive
import Subset
import ProgLang
