sig MedicalDevice {
	isRealizedWith : one CyberPhysicalSystem
}

sig SAMD {
	isRealizedWith : one SoftwareSystem
}

abstract sig CyberPhysicalItem {}
abstract sig CyberPhysicalAggregateItem extends CyberPhysicalItem {}

sig CyberPhysicalSystem extends CyberPhysicalItem {
	topLevel : set CyberPhysicalAggregateItem
}

sig CyberPhysicalCompositeItem extends CyberPhysicalAggregateItem
{
	subSystems : some CyberPhysicalAggregateItem
}

sig MechanicalSubSystem extends CyberPhysicalAggregateItem {}
sig ElectronicalSubSystem extends CyberPhysicalAggregateItem {}
abstract sig SoftwareItem extends CyberPhysicalAggregateItem {}

sig SoftwareSystem extends SoftwareItem
{
	topItems : some AggregateItem
}

abstract sig AggregateItem extends SoftwareItem {}

sig CompositeItem extends AggregateItem
{
	subItems : set AggregateItem
}

sig Unit extends AggregateItem
{
	isImplementedWithSOUP : SOUP
}

sig SOUP extends AggregateItem {
	subSOUP : set SOUP
}


// All SAMD's are realized with exactly one SoftwareSystem
fact 
{
	all p : SAMD | one ss : SoftwareSystem | p.isRealizedWith = ss
}

// for all SoftwareSystem there exist at least one CompositeItem
fact
{
	all s: SoftwareSystem | some ci : CompositeItem | ci in s.topItems
}

// all SOUP and Unit items are part of some CompositeItem
//fact
//{
//	all u : SOUP + Unit | some ci : CompositeItem | u in ci.subItems
//}

// no CompositeItem is (transitely) sub item  of itself
fact
{
	no ci : CompositeItem | ci in ci.^subItems
}

// no SOUP is (transitely) sub SOUP  of itself
fact
{
	no soup : SOUP | soup in soup.^subSOUP
}

// All medical devices are realized with exactly one CyberPhysicalSystem
fact 
{
	all p : MedicalDevice | one cps : CyberPhysicalSystem | p.isRealizedWith = cps
}

// All CyberPhysicalSystem realize exactly one MedicalDevice
fact 
{
	all cps : CyberPhysicalSystem | one p : MedicalDevice | p.isRealizedWith = cps
}

// All CyberPhysicalSystem's have at least one mechnical or electronical subsystem...
fact 
{
	all cps : CyberPhysicalSystem | 
		// Either directly under the top level
		(some ss :  MechanicalSubSystem + ElectronicalSubSystem | ss in cps.topLevel) or 
		// Or transitively under one of the top level composite subsystems
		(some cpcs : CyberPhysicalCompositeItem |  
			some ss : MechanicalSubSystem + ElectronicalSubSystem | cpcs in cps.topLevel and ss in cpcs.^subSystems
		)
}


// for all CyberPhysicalItem's belong to at least one cyberphysical system
fact
{
	all  ci : CyberPhysicalItem - CyberPhysicalSystem | 
		some cps : CyberPhysicalSystem| ci in cps.^(topLevel + subSystems + topItems + subItems)
}

// No CyberPhysicalCompositeItem can transitively include itself
fact
{
	no cpc : CyberPhysicalCompositeItem | cpc in cpc.^subSystems
}

// All composite need to have more than one subsystem
fact
{
	all cpc : CyberPhysicalCompositeItem |  #cpc.subSystems > 1
}

// There should not exist any  CyberPhysicalAggregateItem that's  included directly at  the system level and at the same time is transivelty included in of the toplevel subsystems
fact {
	no a : CyberPhysicalAggregateItem | some s : CyberPhysicalSystem, cpc : CyberPhysicalCompositeItem |  a in cpc.^subSystems and a in s.topLevel
}

// For all CyberPhysicalAggregateItem, and for any CyberPhysicalCompositeItem c1 and c2, if a is included in both c1 and c2, it must be the same item
// Another way of expressing the same fact, an CyberPhysicalAggregateItem should be aggregate in only one CyberPhysicalCompositeItem
fact {
	all a : CyberPhysicalAggregateItem | all c1, c2 : CyberPhysicalCompositeItem | a in c1.^subSystems and a in c2.^subSystems implies c1= c2
}

fact {
	all a : CyberPhysicalAggregateItem |
		no ci1 : CyberPhysicalCompositeItem + CyberPhysicalSystem,  ci2 : AggregateItem + SoftwareSystem |
			a in ci1.(subSystems + topLevel + subItems + topItems + isImplementedWithSOUP) and
			a in ci2.(subSystems + topLevel + subItems + topItems + isImplementedWithSOUP) 
}

pred show (p : MedicalDevice, samd : SAMD) {#SOUP > 2}
run show for 10 but  exactly 1 SAMD
