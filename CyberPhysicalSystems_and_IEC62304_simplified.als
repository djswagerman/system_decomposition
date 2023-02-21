enum Type {System, Unit, Composite}
enum Function {Software, Electronic, Computer, Mechanical, Cyberphysical, Control}


sig MedicalDevice {
	realizedwith: one Item
}
{
	realizedwith.type = System and 
	realizedwith.function = Cyberphysical and
	one s : Item | realizedwith = s
}

sig SoftwareMedicalDevice {
	realizedwith: one Item
}
{
	realizedwith.type = System and 
	realizedwith.function = Software and
	one s : Item | realizedwith = s 
}


sig  Item
{
	type : one Type,
	function : one Function,
	subItems : set Item
}

// A system can't be part of another system
fact
{
	all  i : Item | no s : Item | i.type = System and i in s.subItems
}

// No item can include itself
fact
{
	no i : Item |  i in i.^subItems
}


// Units can't be further decomposed
fact
{
	no i : Item | (i.type = Unit) and #(i.subItems) > 0
}


// A computer, is not further subdivided
fact
{
	all  i : Item | i.function = Computer implies  #(i.subItems) = 0
}



// Software, Mechanical and Electronic subsystems, can only be decomposed within their function (e.g.  their 'children' have the same function
fact
{
	all i : Item |  all c : Item | (i.function in Software+Electronic+Mechanical ) and c in i.^subItems implies c.function = i.function
}

// All cyberphysical and control Items are composites
fact
{
	all  i : Item | (i.function = Cyberphysical or i.function = Control) implies  i.type = Composite or i.type = System
}

// All composite Items have at least two subsystems
fact
{
	all  i : Item | i.type = Composite implies  #(i.subItems) >= 2
}

// Control systems are only subdivided in software or computers
fact
{
	all  i : Item | 
			all c : Item | i.function = Control and
				c in i.^subItems implies (c.function = Software or c.function = Computer)
}

// All control systems have at least one Software component and one Computer
fact
{
	all  i : Item | i.function = Control implies 
				some s : Item | s.function=Software and s in i.subItems and 
				one c : Item | c.function=Computer and c in i.subItems 
}

// All items, except systems, belong to exactly one system
fact
{
	all  i : Item | i.type != System implies one s : Item | s.type = System and i in s.^subItems
}

// All items, expect systems, have only one parent
fact
{
	all  i : Item | i.type != System implies one s : Item | (s.type = Composite or s.type = System) and i in s.subItems
}


pred show (i1, i2, i3, i4, i9 : Item, md :MedicalDevice)
 {
	i1.function=Mechanical and 
	i2.function=Software and
	i3.function = Control and 
	i4.function = Electronic and 
	i9.function =Cyberphysical  and
	i1 in i9.^subItems and 
	i2 in i9.^subItems and 
	i3 in i9.^subItems and 
	i4 in i9.^subItems
}
run show for 9 but exactly 1 MedicalDevice
