abstract sig Product {}

sig MedicalDevice extends Product {
	isRealizedBy: one CyberPhysicalSystem
}

sig SoftwareMedicalDevice extends Product {
	isRealizedBy: one SoftwareSystem
}

abstract sig CyberPhysicalSystemElement {}
sig CyberPhysicalSystem extends CyberPhysicalSystemElement
{
	subSystems : some AggregateSubSystem
}
{
	all cps : CyberPhysicalSystem | some ags : AggregateSubSystem | ags in cps.subSystems
}

abstract sig AggregateSubSystem extends CyberPhysicalSystemElement {}
sig MechanicalSubSystem extends AggregateSubSystem {}
sig ElectronicalSystem extends AggregateSubSystem {}


abstract sig SoftwareItem extends AggregateSubSystem {}

sig SoftwareSystem extends SoftwareItem
{
	subItems : some AggregateItem
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
	all s: SoftwareSystem | some ci : CompositeItem | ci in s.subItems
}


// for all CompositeItem belong to at least one SoftwareSystem
fact
{
	all  ci : CompositeItem | some s : SoftwareSystem | ci in s.subItems
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


pred show (s : SoftwareSystem) {#SoftwareSystem.subItems > 1}
run {} for 10 but exactly 1 SoftwareSystem, 2 SOUP, exactly 3 Unit
