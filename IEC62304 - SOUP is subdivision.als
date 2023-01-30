abstract sig AbstractItem {}

sig SoftwareItem extends AbstractItem
{
	subItems : set AbstractItem
}
sig SoftwareSystem extends SoftwareItem {}
sig SOUP extends SoftwareItem {}

sig Unit extends AbstractItem {}


// No abstract item can (acyclic) include itselve
fact 
{
	no i : AbstractItem | i in i.^subItems
}

// A SoftwareSystem is never in a subitem
fact 
{
	no s : SoftwareSystem | some i : AbstractItem | s in i.subItems
}

// All abstractitems are part of a system (with the execption of SoftwareSystem)
fact 
{
	all i : AbstractItem - SoftwareSystem | some s : SoftwareSystem | i in s.^subItems
}

// A system is never directly subdivided towards Units
fact 
{
	all u : Unit | no sys : SoftwareSystem | u in sys.subItems
}

// A system is never directly subdivided to SOUP
fact 
{
	all s : SOUP | no sys : SoftwareSystem | s in sys.subItems
}


// SOUP can only be further subdivided to SOUP (and not to units)
fact 
{
	all s : SOUP | no i : AbstractItem | i in s.subItems and i not in SOUP
}


// Items have a minumum of 2 subItems
fact {
	all i : SoftwareItem - SOUP | #(i.subItems) > 2
}


pred show (s : SoftwareSystem) {#SOUP > 2 and #SoftwareItem > 2}
run show for 10
