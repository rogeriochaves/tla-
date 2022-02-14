---- MODULE MC ----
EXTENDS learning, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT definitions Acceptor
const_1628354875209124000 == 
{a1, a2, a3}
----

\* MV CONSTANT definitions RM
const_1628354875209125000 == 
{r1, r2}
----

\* SYMMETRY definition
symm_1628354875209126000 == 
Permutations(const_1628354875209124000) \union Permutations(const_1628354875209125000)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
const_1628354875209127000 == 
{0, 1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
const_1628354875209128000 == 
{{a1, a2}, {a1, a3}, {a2, a3}}
----

=============================================================================
\* Modification History
\* Created Sat Aug 07 18:47:55 CEST 2021 by rchaves
