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
	function : one Function
}

sig CompositeItem extends Item
{
	subSystems : set Item
}

sig System extends CompositeItem {}

sig Unit extends Item {}
{
	function not in Software + Cyberphysical
}

sig SoftwareUnit extends Unit
{
	usesSOUPLibraries : set SOUPLibrary
}
{
	function = Software
}

sig Computer extends Item {}
{
	function = Electronic
}

sig SOUP extends Item {}
{
	function = Software
}

sig SOUPLibrary {}
{
	some u : Unit | this in u.usesSOUPLibraries
}

// No composite can include itself
fact
{
	no i: CompositeItem | i in i.^subSystems
}

// All items, except for a system, belong to some system
fact
{
	all i: Item - System | some s : System | i in s.^subSystems
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

// All descendants of a system, that have the same function as their parent, can't also be Systems (but are Units or Composites)
fact
{
	all  s : System | all i : Item | i in s.^subSystems and s.function = i.function implies not i in System
}

// All descendants of a system, that have the same function as their parent, can't also be Systems (but are Units or Composites)
fact
{
	no  s : System, md : MedicalDevice, samd : SoftwareMedicalDevice |
		s.function =  Software and
		s in md.realizedwith.^subSystems and
		s = samd.realizedwith
}

fact
{
	all s : System | s.funtion = Cyberphysical implies
		some md : MedicalDevice | md.realizedwith = s
}

pred show (i1, i2, i3, i4, i9 : Item, md : MedicalDevice, samd : SoftwareMedicalDevice)
{
	(
		i1.function = Electronic and
		i2.function = Software and
		i9 = md.realizedwith and
		i1 in i9.^subSystems and
		i2 in i9.^subSystems
	) or
	(
		i1.function = Software and
		i9 = samd.realizedwith and
		i1 in i9.^subSystems
	)
}
run show for 15 but exactly  1 MedicalDevice, exactly 1 SoftwareMedicalDevice
