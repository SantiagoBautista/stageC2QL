module Reproductibility

import Privy
import C2QL

||| For reproductibility of research,
||| I will declare in this file the counter-examples
||| cited in section 6 of Cherrueau's thesis and verify
||| that they do not compile

-- La création de termes C2QL ne produit pas d'erreur :/

envImplemError : C2QL -> C2QL
envImplemError = Select (Like N "C*") .
                  Project [N, A] .
                  Defrag (Hole_ 0, Hole_ 1) .
                  Frag [N]

foo: Attribute
foo = ("foo", TEXT)

envSpecError : C2QL
envSpecError = Crypt foo AES (Rel RendezVous)

-- Par contre la création de termes Privy soulève bien les erreurs
-- (cf lignes commentées dans Privy.idr)
