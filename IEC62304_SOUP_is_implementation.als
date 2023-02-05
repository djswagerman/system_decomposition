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

sig SOUP  {
	subSOUP: SOUP
}
fact { no soup: SOUP | soup in soup.^subSOUP}



sig Unit extends Item {
	isImplementedWith : set SOUP
}

pred show (s : SOUP) {#SOUP > 2}
run {} for 10 but 2 SOUP
