sig Item {}

sig CompositeItem extends Item {
	subdividesInto : set Item
}

sig System extends CompositeItem {}
sig SOUP extends CompositeItem {}
sig Unit extends Item {}


pred show (s : System) {#Unit > 2 and #SOUP > 2}
run {} for 6 but exactly 2 Unit, 2 System
