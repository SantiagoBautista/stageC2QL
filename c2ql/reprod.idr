module Reproductibility

import Privy
import C2QL

||| For reproductibility of research,
||| I will declare in this file the counter-examples
||| cited in section 6 of Cherrueau's thesis and verify
||| that they do not compile

envImplemError : C2QL -> C2QL
envImplemError = Select (Like N "C*") .
                  Project [N, A] .
                  Defrag (Hole_ 0, Hole_ 1) .
                  Frag [N]
