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
sig SoftwareSubSystem extends CyberPhysicalAggregateItem {}

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

// All CyberPhysicalSystem's have at least one mechnical or eletronical subsystem...
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
	all a : CyberPhysicalAggregateItem | all c1, c2 : CyberPhysicalCompositeItem | a in c1.subSystems and a in c2.subSystems implies c1= c2
}

pred show (p : MedicalDevice) {#ElectronicalSubSystem > 0 and #MechanicalSubSystem > 0 and #CyberPhysicalCompositeItem > 1 }
run show for 10 but 1 MedicalDevice
