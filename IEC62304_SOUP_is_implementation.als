abstract sig Item {}
fact 
{
	all i : Item - System.root | some c : CompositeItem | i in c.subdividesInto
}

sig CompositeItem extends Item {
	subdividesInto : set Item
}
fact { no ci : CompositeItem | ci in ci.^subdividesInto }

sig System {
	root: one CompositeItem
}
fact { all ci : CompositeItem | #(ci.subdividesInto) > 1 }

sig SOUP extends Item {
	subSOUP: SOUP
}
fact { no s: SOUP | s in s.^subSOUP}


sig Unit extends Item {
	isImplementedWith : SOUP
}

pred show (s : System) {}
run {} for 6 but exactly 2 System
