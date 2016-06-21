# Megadeth

An experimental automatic and aggressive instance derivator in Haskell using
Template Haskell. It is a small part of the [QuickFuzz](http://QuickFuzz.org/)
project.
 
*Mega Derivation TH* (MegaDeTh)
gives the user an **aggressive** way to derive instances for all the intermediate
nested types that are needed to make the top-level instance work.

### Example

Given the follow type:
    
    data GifFile = GifFile { 
          gifHeader      :: GifHeader,
          gifImages      :: [(Maybe GraphicControlExtension,
                              GifImage)],
          gifLoopingBehaviour :: GifLooping
        }

We can derive its `show` instance with the help of
[Derive](http://hackage.haskell.org/package/derive): 

    $(devShow ''GifFile)

## Authors

* Pablo **Buiras** ([Chalmers University of Technology](http://www.chalmers.se/en/Pages/default.aspx))
* Martín **Ceresa** ([CIFASIS-Conicet](http://cifasis-conicet.gov.ar/))
* Gustavo **Grieco** ([CIFASIS-Conicet](http://cifasis-conicet.gov.ar/) and [VERIMAG](http://www-verimag.imag.fr/?lang=en))

## Requirements

 * A modern version of GHC (e.g 7.10)
 * [Stack](www.haskellstack.org/)

## Instalation

    $ stack install
