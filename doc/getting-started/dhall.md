# Some caveats regarding Dhall
Package name: dhall

Version used: 1.5.1

[Link](http://hackage.haskell.org/package/dhall-1.15.1)


## When you don't derive the show instance of the datatype that you want to parse, dhall will not print anything on the console.

Say you have some datatype like this:

```
data Config = Config {
      walletPort   :: !Natural
    , walletDBPath :: !Text
    }
```

and you forgot to derive an show instance of it.
When you parse the dhall file and try to print the result, the console does not warn you about
missing show instance. It returns nothing at all.


## Breaking change from 1.1.1 to 1.5.1

There was a breaking change upon 1.14 release where the grammar of Natural and Integer was swapped.
You can check the release notes [here](https://github.com/dhall-lang/dhall-haskell/releases/tag/1.14.0)

This means I had to switch some of the types (e.g. WalletPort) from Integer to Natural

## Defining an instance of Interpret with defaultInterpretOptions causes infinite loop

In order to parse Dhall file, you'll need to define an typeclasss instance of `Interpret`, similiar [aeson](http://hackage.haskell.org/package/aeson-1.4.1.0/docs/Data-Aeson.html).


There's is an way to easier way to define an instance of it using [defaultInterpretOptions](http://hackage.haskell.org/package/dhall-1.15.1/docs/Dhall.html#v:defaultInterpretOptions).

But for some reason, this causes infinite loop. Currently looking into it.