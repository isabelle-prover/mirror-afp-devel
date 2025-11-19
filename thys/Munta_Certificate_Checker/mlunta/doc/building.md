### Building MLunta
<!-- To build **MLunta** one needs to have the newest versions of -->
<!-- either `poly` **and** `polyc` or `mlton`installed. -->

#### With MLton
If you have the newest version of `mlton` installed the checker can be build by
running `make build_checker`.

#### With Poly/ML
(Even though one maybe has the polyml package installed under Ubuntu
Versions before Ubuntu Xenial it could be that polyc is not installed if this is
the case one must install polyml from source so polyc can be used)
To build the checker with `polyc` run `make build_checker_poly`
