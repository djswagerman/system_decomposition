enum Function {Software, Electronic, Mechanical, Cyberphysical, Control}
enum TopLevel {Yes, No}

abstract sig MedicalDevice {}

// A CyberPhysicalMedicalDevice is realized with a CyberPhysicalSystem
sig CyberPhysicalMedicalDevice extends MedicalDevice 
{
	realizedwithCyberPhysicalSystem : one CyberPhysicalSystem
}
{
	one s : CyberPhysicalSystem | realizedwithCyberPhysicalSystem = s and s.isTopLevel = Yes
}

// A SoftwareMedicalDevice is realized with a SoftwareSystem
sig SoftwareMedicalDevice  extends MedicalDevice
{
	realizedwithSoftwareSystem: one SoftwareSystem
}
{
	one s : SoftwareSystem | realizedwithSoftwareSystem = s and s.isTopLevel = Yes
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
abstract sig System extends CompositeItem {
	isTopLevel : TopLevel
}

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

sig SOUP extends Item
{
	subSOUP : set SOUP
}
{
	function = Software
	this not in subSOUP
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
	function in Software
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
	all  s : SoftwareSystem | one samd : SoftwareMedicalDevice |  s.isTopLevel = Yes implies s in samd.realizedwithSoftwareSystem
}

// All CyberPhysicalSystem realize exactly one CyberPhysicalMedicalDevice
fact
{
	all  s : CyberPhysicalSystem | one md : CyberPhysicalMedicalDevice |   s.isTopLevel = Yes implies s in md.realizedwithCyberPhysicalSystem
}

// No item can include itself
fact
{
	no i : Item |  i in i.^subSystems
}

// A Top level system is never a subsystem
fact
{
	no s : System | some c : CompositeItem | s.isTopLevel = Yes and s in c.subSystems
}

// All items, expect top level systems, have only one parent
// (systems do not have a parent)
fact
{
	all  i : Item  | not (i in System and i.isTopLevel = Yes)  implies lone c : CompositeItem |  i in c.subSystems
}

// All items, except top level systems, belong to exactly one system
fact
{
	all  i : Item  | not (i in System and i.isTopLevel = Yes)  implies one s : System | s.isTopLevel = Yes and  i in s.^subSystems
}

// Software, Mechanical and Electronic subsystems, can only be decomposed within their function 
// (e.g.  their 'children' have the same function
fact
{
	all i : Item |  all c : Item | (i.function in Software+Electronic+Mechanical) and c in i.^subSystems implies c.function = i.function
}

// SOUP can only be decomposed to SOUP
//fact
//{
//	all s : SOUP |  all c : Item | c in s.^subSystems implies c in SOUP
//}

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
	i1 in SOUP and i2 in i1.subSOUP and
	i3 in SoftwareSystem and
	i3 in md.realizedwithCyberPhysicalSystem.^subSystems
}

run show for 8 but exactly 1 CyberPhysicalMedicalDevice,  exactly 1 SoftwareMedicalDevice
