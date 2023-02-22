enum Function {Software, Electronic, Mechanical, Cyberphysical, Control}

abstract sig MedicalDevice {}

sig CyberPhysicalMedicalDevice extends MedicalDevice 
{
	realizedwithCyberPhysicalSystem : one CyberPhysicalSystem
}
{
	one s : CyberPhysicalSystem | realizedwithCyberPhysicalSystem = s
}

sig SoftwareMedicalDevice  extends MedicalDevice
{
	realizedwithSoftwareSystem: one SoftwareSystem
}
{
	one s : SoftwareSystem | realizedwithSoftwareSystem = s
}

abstract sig  Item
{
	function : one Function
}

sig CompositeItem extends Item
{
	subSystems : set Item
}

abstract sig System extends CompositeItem {}

sig CyberPhysicalSystem extends System {}
{
	function = Cyberphysical
}

sig SoftwareSystem extends System {}
{
	function = Software
}

sig Unit extends Item {}
{
	function in Software + Electronic + Mechanical + Computer
}

sig Computer extends Item {}
{
	function = Electronic
}

sig SOUP extends Item {}
{
	function = Software
}

// 1. No item can include itself
fact
{
	no i : Item |  i in i.^subSystems
}

// 2. A System can't be part of something else
//fact
//{
//	no s : System | some c : CompositeItem | s in c.subSystems
//}

// 3. All items, except systems, belong to exactly one system
//fact
//{
//	all  i : Item - System | one s : System |  i in s.^subSystems
//}


// 4. All SoftwareSystems realize exactly one SoftwareMedicalDevice
fact
{
	all  s : SoftwareSystem | one samd : SoftwareMedicalDevice |  s in samd.realizedwithSoftwareSystem
}

// 5. All CyberPhysicalSystem realize exactly one CyberPhysicalMedicalDevice
fact
{
	all  s : CyberPhysicalSystem | one md : CyberPhysicalMedicalDevice |  s in md.realizedwithCyberPhysicalSystem
}

// 6. All items, expect systems, have only one parent
// (systems do not have a parent)
fact
{
	all  i : Item - System | one c : CompositeItem |  i in c.subSystems
}

// 7. Software, Mechanical and Electronic subsystems, can only be decomposed within their function 
// (e.g.  their 'children' have the same function
fact
{
	all i : Item |  all c : Item | (i.function in Software+Electronic+Mechanical ) and c in i.^subSystems implies c.function = i.function
}

// 8. All composite Items have at least two subsystems
fact
{
	all  i : CompositeItem | #(i.subSystems) >= 2
}

// 9. Control systems are only subdivided in software or computers
fact
{
	all  i : Item | 
			all c : Item | i.function = Control and
				c in i.^subSystems implies (c.function = Software or c in Computer)
}

// 10. All software items that have a 'non-software' parent, need to have a sibling that is a computer
fact
{
	all  i : Item, p : CompositeItem |
		{
			i.function = Software
			p.function in Cyberphysical + Control
			i in p.subSystems
		} implies one c : Computer | c in p.subSystems
}

pred show (md : CyberPhysicalMedicalDevice, i1, i2, i3, i4 : Item) 
{
	(
		i2 in SoftwareSystem and
		i3 in CompositeItem and i3.function = Control and
		i4 in CompositeItem - System and i1.function = Software 
	)
}


run show for 8 but exactly 1 CyberPhysicalMedicalDevice, 0 SoftwareMedicalDevice
