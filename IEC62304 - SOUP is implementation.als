abstract sig AbstractItem {
}

sig SoftwareItem extends AbstractItem
{
	subItems : set AbstractItem
}
sig SoftwareSystem extends SoftwareItem {}
sig SOUP {}

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
	all i : AbstractItem - SoftwareSystem | some s : SoftwareSystem | i in s.^subItems
}


// No abstract item, can be the subitem of more than one other abstractItem
fact 
{
	all i1 : AbstractItem - SoftwareSystem | one i2 : SoftwareItem | i1 in i2.subItems 
}


// Items have a minumum of 2 subItems
fact {
	all i : SoftwareItem | #(i.subItems) > 2
}

pred show (s : SoftwareSystem) {#SOUP > 2 and #SoftwareItem > 2}
run show for 10
