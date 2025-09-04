# ITV


# Installation

> Linux:
`pip install --user -r requirements.txt` or `pip3 install --user -r requirements.txt`

> MacOS
`pip install -r requirements.txt` or `pip3 install -r requirements.txt`

![Alt text](./diagram.png)


> Note: Need to add nextTo(*node*) as a parameter in BNF. We do not need to edit SyntaxBNF.

### Convert Derivations in input.s to look like output.s

> Using Python 
>
> Each formula must be categorized into tcf, fof, or thf
>

> Each formula must include **name**, **formula_role**, **formula**, **inference** (with **inference_rule**, **level**, **parents**)
> - **level** is under **useful_info**
>

### Use GraphViz to show correct orientation of graph using nextTo(...)

> Look into GraphViz docs and Jack's code
