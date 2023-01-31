sig Item {
	subdividesInto : set Item
}

sig System extends Item {}
sig SOUP extends Item {}
sig Unit extends Item {}


pred show (s : System) {#Unit > 2 and #SOUP > 2}
run {} for 10 but 1 System
