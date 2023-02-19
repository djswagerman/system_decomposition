enum Function {Software, Electronic, Mechanical, Cyberphysical, Control}

sig MedicalDevice {
	realizedwith: one System
}
{
	realizedwith.function = Cyberphysical and
	one s : Item | realizedwith = s
}

sig SoftwareMedicalDevice {
	realizedwith: one System
}
{
	realizedwith.function = Software and
	one s : Item | realizedwith = s
}

abstract sig  Item
{
	function : one Function,
}

sig CompositeItem extends Item
{
	subSystems : set Item
}

sig System extends CompositeItem {}

sig Unit extends Item
{
	usesSOUPLibraries : set SOUP
}

sig Computer extends Item
{
}

sig SOUP extends Item
{
}
{
	function = Software
}

// No composite can include itself
fact
{
	no i: CompositeItem | i in i.^subSystems
}

// All items, except for a system, belong to some system
fact
{
	all i: Item - System|  some s : System | i in s.^subSystems
}

// All items have one parent
fact
{
	all i: Item - System|  one c : CompositeItem | i in c.subSystems
}

// Software, Mechanical and Electronic subsystems, can only be decomposed within their function (e.g.  their 'children' have the same function
fact
{
	all i : Item |  all c : Item | (i.function in Software+Electronic+Mechanical ) and c in i.^subSystems implies c.function = i.function
}

// All composite Items have at least two subsystems
fact
{
	all  i : CompositeItem | #(i.subSystems) >= 2
}

// Control systems are only subdivided in software or computers
fact
{
	all  i : Item | 
			all c : Item | i.function = Control and
				c in i.^subSystems implies (c.function = Software or c = Computer)
}

// All control systems have at least one Software component and one Computer
fact
{
	all  i : Item | i.function = Control implies 
				some s : Item | s.function=Software and s in i.subSystems and 
				one c : Item | c = Computer and c in i.subSystems 
}

// All items, expect cyberphyscal systems, have only one parent
fact
{
	all  i : Item | not (i in System and i.function = Cyberphysical) implies one c : CompositeItem | i in c.subSystems
}

// All systems
fact
{
	all  s : System | some i : Item | i in s.subSystems implies i.function != s.function
}

pred show (i1, i2, i3, i4, i9 : Item, md : MedicalDevice)
 {
	i1.function=Mechanical and 
	i2.function=Software and
	i3.function = Control and 
	i4.function = Electronic and 
	i9.function =Cyberphysical  and
	i1 in i9.^subSystems and 
	i2 in i9.^subSystems and 
	i3 in i9.^subSystems and 
	i4 in i9.^subSystems
}
run show for 9 but exactly 1 MedicalDevice
