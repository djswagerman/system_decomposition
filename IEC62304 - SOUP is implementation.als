abstract sig AbstractItem {
}

sig SoftwareItem extends AbstractItem
{
	subItems : set AbstractItem
}
sig SoftwareSystem extends SoftwareItem {}
sig SOUP extends AbstractItem {}

sig Unit extends AbstractItem
{
	implementedWithSOUP : SOUP
}

// No abstract item can (acyclic) include itselve
fact 
{
	no i : AbstractItem | i in i.^subItems
}

// A system is never a subitem
fact 
{
	no s : SoftwareSystem | some i : AbstractItem | s in i.subItems
}

// All abstractitems are part of a system (with the execption of 'systems')
fact 
{
	all i : AbstractItem - SoftwareSystem - SOUP | some s : SoftwareSystem | i in s.^subItems
}

// SOUP is part of one or more units
fact 
{
	all s : SOUP | some u: Unit | s in u.implementedWithSOUP
}

// A system is never directly subdivided to SOUP
fact 
{
	all s : SOUP | no sys : SoftwareSystem | s in sys.subItems
}

// A system is never directly subdivided to Units
fact 
{
	all u : Unit | no sys : SoftwareSystem | u in sys.subItems
}

// SOUP is never part of a software Item
fact 
{
	all s : SOUP | no si : SoftwareItem | s in si.subItems
}

// Items have a minumum of 2 subItems
fact {
	all i : SoftwareItem | #(i.subItems) > 2
}

pred show (s : SoftwareSystem) {}
run show for 10 but exactly 3 SOUP
