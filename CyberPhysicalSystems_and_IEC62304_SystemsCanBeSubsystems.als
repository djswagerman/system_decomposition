enum Function {Software, Electronic, Mechanical, Cyberphysical, Control}

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

// SOUP Items can reside at all levels (a SOUP Item could be further subdivided)
sig SOUP extends CompositeItem {}
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
	all  s : SoftwareSystem | 
		(
			one samd : SoftwareMedicalDevice |  s in samd.realizedwithSoftwareSystem or
			no cps : CyberPhysicalSystem | s in cps.^subSystems
		) or

		(
			no samd : SoftwareMedicalDevice |  s in samd.realizedwithSoftwareSystem or
			one cps : CyberPhysicalSystem | s in cps.^subSystems
		) 
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

// A CyberPhysicalSystem is never a subsystem
fact
{
	no s : CyberPhysicalSystem | some c : CompositeItem | s in c.subSystems
}


// All items, expect systems, have only one parent
// (systems do not have a parent)
fact
{
	all  i : Item - CyberPhysicalSystem | one c : CompositeItem |  i in c.subSystems
}

// All items, except systems, belong to exactly one system
fact
{
	all  i : Item - CyberPhysicalSystem | one s : CyberPhysicalSystem |  i in s.^subSystems
}

pred show (md : CyberPhysicalMedicalDevice, samd : SoftwareMedicalDevice, i1, i2, i3, i4 : Item) 
{
	(
		i1 in SoftwareSystem
	)
}

run show for 10 but exactly 1 CyberPhysicalMedicalDevice
