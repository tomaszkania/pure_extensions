import PureEmbeddings

/-! Print the four public signatures and their kernel axiom dependencies. -/
#check PureEmbeddings.theoremA
#check PureEmbeddings.theoremB
#check PureEmbeddings.Groups.theoremC
#check PureEmbeddings.theoremD
#print axioms PureEmbeddings.theoremA
#print axioms PureEmbeddings.theoremB
#print axioms PureEmbeddings.Groups.theoremC
#print axioms PureEmbeddings.theoremD
#print axioms PureEmbeddings.extension_iff
#print axioms PureEmbeddings.PrimeAntichain.lower
#print axioms PureEmbeddings.SupportedModules.supported_pureInjective
