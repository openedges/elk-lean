import Elk.Graph.Enum
/-!
# `org.eclipse.elk.core.options.TopdownSizeApproximator`

The enumeration of the built-in approximators (`ITopdownSizeApproximator`
implementations). Their `getSize` implementations read `CoreOptions`
properties and therefore live in `Elk.Core.Options.TopdownSizeApproximatorUtil`
(`TopdownSizeApproximator.getSize`) to avoid an import cycle with `CoreOptions`.
-/
namespace Elk.Core.Options

/-- `org.eclipse.elk.core.options.TopdownSizeApproximator`
(also stands for the `ITopdownSizeApproximator` interface, see module doc). -/
elk_enum TopdownSizeApproximator := countChildren lookaheadLayout fixedIntegerRatioBoxes layoutNextLevel

end Elk.Core.Options
