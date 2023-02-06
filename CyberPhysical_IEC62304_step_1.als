sig MedicalDevice {
	isRealizedWith : one CyberPhysicalSystem
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

// for all SoftwareSystem there exist at least one CompositeItem
fact
{
	all s: SoftwareSystem | some ci : CompositeItem | ci in s.topItems
}


// for all CompositeItem belong to at least one SoftwareSystem
fact
{
	all  ci : CompositeItem | some s : SoftwareSystem | ci in s.topItems
}

// all SOUP and Unit items are part of some CompositeItem
fact
{
	all u : SOUP + Unit | some ci : CompositeItem | u in ci.subItems
}

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

// All CyberPhysicalAggregateItem's belong to 'something'
fact 
{
	all cpa : CyberPhysicalAggregateItem |
		// either a CyberPhysicalSystem
		some cps : CyberPhysicalSystem | cpa in cps.topLevel or

		// or (transitevely) in a CyberPhysicalCompositeItem that's
		some cpcs : CyberPhysicalCompositeItem |  cpcs in cps.topLevel  and cpa in cpcs.^subSystems
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
	all a : SoftwareItem |
		some c1 : CyberPhysicalCompositeItem, c2 : CompositeItem
			a in c1.^(subItems + topItems + subSystems + topLevel)  and a in c2.^(subItems + topItems + subSystems + topLevel)  implies c1= c2) or
}

//fact {
//	all a1, a2 : CyberPhysicalItem, s : CyberPhysicalSystem | 
//		a1 in s.^(subItems + topItems + subSystems + topLevel) and
//		a2 in a1.(subItems + topItems + subSystems + topLevel) implies 
//			not (a2 in (a1.^(subItems + topItems + subSystems + topLevel) - a1.(subItems + topItems + subSystems + topLevel)))
//}

//fact
//{
//	no a1, a2, a3 : CyberPhysicalItem | 
//		a2 in a1.^(subItems + topItems + subSystems + topLevel) and 
//		a3 in a2.^(subItems + topItems + subSystems + topLevel) and
//		a3 in a1.(subItems + topItems + subSystems + topLevel) 
//}
//

//fact{
//	all i : CyberPhysicalAggregateItem  | one c : CyberPhysicalCompositeItem +  CyberPhysicalSystem | i in c.(subItems + topItems + subSystems + topLevel) 
//}

pred show (p : MedicalDevice) {#ElectronicalSubSystem > 0 and #MechanicalSubSystem > 0 and #CyberPhysicalCompositeItem > 1 and #Unit > 1 }
run show for 10 but 1 MedicalDevice
