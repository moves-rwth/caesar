# HeyVL Examples

## Geometric Loop

The expected value of the counter `c` increases by at most one. [**Open in editor**](command:caesar.openExampleFileBeside)

```heyvl
coproc geo(init_c: UInt) -> (c: UInt)
    pre init_c + 1
    post c
{
    c = init_c
    var cont: Bool = true
    @invariant(ite(cont, c + 1, c))
    while cont {
        var prob_choice: Bool = flip(0.5)
        if prob_choice {
            c = c + 1
        } else {
            cont = false
        }
    }
}
```

## More Examples

You can find more examples in our [Zoo of HeyVL Examples](https://www.caesarverifier.org/docs/getting-started/zoo-of-heyvl-examples).
