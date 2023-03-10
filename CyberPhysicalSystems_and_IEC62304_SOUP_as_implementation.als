enum Function {Software, SOUP, Electronic, Mechanical, Cyberphysical, Control}

abstract sig MedicalDevice {}

// A CyberPhysicalMedicalDevice is realized with a CyberPhysicalSystem
sig CyberPhysicalMedicalDevice extends MedicalDevice 
{
	realizedwithCyberPhysicalSystem : one CyberPhysicalSystem
}
{
	one s : CyberPhysicalSystem | realizedwithCyberPhysicalSystem = s
}

// A SoftwareMedicalDevice is realized with a SoftwareSystem
sig SoftwareMedicalDevice  extends MedicalDevice
{
	realizedwithSoftwareSystem: one SoftwareSystem
}
{
	one s : SoftwareSystem | realizedwithSoftwareSystem = s
}

// An Item is not directly instantiated, and has a 'function' or 'discipline'
abstract sig  Item
{
	function : one Function
}

// CompositeItems are Items that can be further subdivided
sig CompositeItem extends Item
{
	subSystems : set Item
}

// A system is a special CompositeItem (no parent)
abstract sig System extends CompositeItem {}

// There are two types of system, a CyberPhysicalSystem...
sig CyberPhysicalSystem extends System {}
{
	function = Cyberphysical
}

// ...And a SoftwareSystem
sig SoftwareSystem extends System {}
{
	function = Software
}

// A unit is not further subdivided. There are three cyberphysical unit types
sig Unit extends Item {}
{
	function in  Electronic + Mechanical + Computer
}

// And there are SoftwareUnits. While software units are not further subdivided, they can be build using SOUP libraries
sig SoftwareUnit extends Item
{
	usesSOUPLibary : set SOUPLibary
}
{
	function in Software + SOUP
}

// A Computer is a special sort of Electronic Unit
sig Computer extends Item {}
{
	function = Electronic
}

// A SOUP library (source code or assemblies) can be used inside a unit
sig SOUPLibary {}


//***************** Facts ***************


// All SoftwareSystems realize exactly one SoftwareMedicalDevice
fact
{
	all  s : SoftwareSystem | one samd : SoftwareMedicalDevice |  s in samd.realizedwithSoftwareSystem
}

// All CyberPhysicalSystem realize exactly one CyberPhysicalMedicalDevice
fact
{
	all  s : CyberPhysicalSystem | one md : CyberPhysicalMedicalDevice |  s in md.realizedwithCyberPhysicalSystem
}

// No item can include itself
fact
{
	no i : Item |  i in i.^subSystems
}

// A System is never a subsystem
fact
{
	no s : System | some c : CompositeItem | s in c.subSystems
}

// All items, expect systems, have only one parent
// (systems do not have a parent)
fact
{
	all  i : Item - System | one c : CompositeItem |  i in c.subSystems
}

// All items, except systems, belong to exactly one system
fact
{
	all  i : Item - System | one s : System |  i in s.^subSystems
}

// Software, Mechanical and Electronic subsystems, can only be decomposed within their function 
// (e.g.  their 'children' have the same function
fact
{
	all i : Item |  all c : Item | (i.function in Software+Electronic+Mechanical+SOUP ) and c in i.^subSystems implies c.function = i.function
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
				c in i.^subSystems implies (c.function = Software or c in Computer)
}

// All software items that have a 'non software' parent, need to have a sibling that is a computer
// This rule ensures that the 'highest' level software item, has at least one computer as a sibling that it could run on.
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
		i1 in CompositeItem and i1.function = Software and
		i1 in md.realizedwithCyberPhysicalSystem.^subSystems
	)
}

run show for 10 but exactly 1 CyberPhysicalMedicalDevice,  exactly 1 SoftwareMedicalDevice
