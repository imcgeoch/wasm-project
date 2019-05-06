"""
Given a list of enum type type constructors, implement decEq
"""

from typing import List, Tuple, Dict, Set
from argparse import ArgumentParser
from sys import argv

class Indent:
    def __init__(self, width=4, depth=0):
        self.depth = depth
        self.width = width
        self.indent_str = ' ' * width

    def push(self):
        self.depth += 1

    def pop(self):
        self.depth -= 1
        if self.depth < 0:
            raise RuntimeError("Indent popped from empty")

    def __call__(self, s=''):
        return str(self) + str(s)

    def __str__(self):
        return self.indent_str * self.depth

class DecEqProofWriter:
    def __init__(self, type_name : str,
                       val_constructors : List[Tuple[str, int]]):
        """
        :type_name: name of the Idris type we are proving DecEq for
        :val_constructors: a list of the value constructors/arg length tuples.

        For instance, if we wanted to represent the data type

            data Foo = Bar | Baz Int | Blammo String Int

        we would want to pass `"Foo"` in for type name, and pass in
        `[("Bar", 0), ("Baz", 1), ("Blammo", 2)]` for the `val_constructors`
        argument.
        """
        self.type_name = type_name
        self.vcs : Dict[str, int] = {}
        self.indent = Indent(depth=1)
        self.header = "DecEq {} where".format(self.type_name)

        for (v, a) in val_constructors:
            if v in self.vcs:
                raise RuntimeError("Duplicate val constructor {} found".format(v))
            if a < 0:
                raise RuntimeError("Negative arguments length {} found".format(a))
            self.vcs[v] = a

        # (VC, argnum) -> (name, body)
        self.injective_lemmas : Dict[Tuple[str, int], Tuple[str, str]] = {}
        # (VC1, VC2) -> (name, body)
        self.not_equals_lemmas : Dict[Tuple[str, str], Tuple[str, str]] = {}
        self.cases : List[str] = []
        self.visited : Set[Tuple[str, str]] = set()
        self.argnames = 'abcdefghijklmnopqrstuvwxyz'

    def compare_two(self, vc1, vc2):
        '''
        Generate code for these two value constructors
        '''
        if (vc1, vc2) in self.visited:
            Warning("Already visited pair ({}, {})! Nothing done".format(vc1, vc2))
            return
        self.visited.add((vc1, vc2))

        # Get unique names for the arguments of each value constructor
        args1 = [ch for ch in self.argnames[:self.vcs[vc1]]]
        if self.vcs[vc2] == 0:
            args2 = []
        else:
            args2 = [ch for ch in self.argnames[-self.vcs[vc2]:]]

        if len(args1) + len(args2) > 26:
            raise RuntimeError("Too many arguments, name collision!")

        arg1 = "({} {})".format(vc1, ' '.join(args1))
        arg2 = "({} {})".format(vc2, ' '.join(args2))

        dec_eq = "decEq {} {}".format(arg1, arg2)
        case_body = "?autogen_hole_{}_{}".format(vc1, vc2)

        def proc_args(args, n):
            yes = "Yes Refl  => {}"
            no  = "No contra => No $ \h => (contra . {}) h)"
            self.write_injective_lemma(vc1, n)
            if n == len(args):
                return "Yes Refl"
            else:
                # is a (name, body) pair for the appropriate injectivity lemma
                inj_lem = self.injective_lemmas[(vc1, n)]
                self.indent.push()
                a,b = args[n]
                case = '\n'.join(
                        ["(case decEq {} {} of".format(a,b),
                         self.indent(yes.format(proc_args(args, n + 1))),
                         self.indent(no.format(inj_lem[0]))
                        ])
                self.indent.pop()
                return case

        if vc1 == vc2:
            args2 = [a + "'" for a in args1]
            arg2 = "({} {})".format(vc2, ' '.join(args2))
            dec_eq = "decEq {} {}".format(arg1, arg2)
            case_body = proc_args(list(zip(args1, args2)), 0)

        elif (vc2, vc1) in self.not_equals_lemmas:
            name, _ = self.not_equals_lemmas[(vc2, vc1)]
            case_body = "No $ negEqSym {}".format(name)

        else:
            name = "not_{}_{}".format(vc1, vc2)
            tp = "({} {}) = ({} {}) -> Void".format(vc1, ' '.join(args1), vc2, ' '.join(args2))

            sig = "{} : {}".format(name, tp)
            impl = "{} Refl impossible".format(name)

            docstring = '''
||| Auto generated theorem proving that {} is not equal to {}.
||| Generated to assist in proving {}'''.format(vc1, vc2, name).strip()
            lemma = '\n'.join([docstring, 'total ' + sig, impl])
            self.not_equals_lemmas[(vc1, vc2)] = (name, lemma)
            case_body = "No {}".format(name)

        case = self.indent("{} = {}".format(dec_eq, case_body))
        self.cases.append(case)

    def write_injective_lemma(self, vc, n):
        '''
        Writes the injectivity lemmas for a value constructor

        Parameters:
            :vc: name of the value constructor
            :n: which arg we are proving injectivity on
        '''
        ls = []
        num_args = self.vcs[vc]
        for i in range(num_args):
            name = "{}_injective_on_arg{}".format(vc.lower(), i)
            docstring = '''
||| Auto generated theorem proving injectivity of value constructor {}.
||| Generated to assist in proving {}'''.format(vc, name).strip()
            n1, n2, as1, as2 = self.make_arg_strings(num_args, i, 'x')
            typ = "({} {}) = ({} {}) -> {} = {}".format(vc, as1, vc, as2, n1, n2)
            lem = '\n'.join([docstring, 'total {} : {}'.format(name, typ), '{} Refl = Refl'.format(name)])
            ls.append(lem)
            self.injective_lemmas[(vc,i)] = (name, lem)
        return ls

    def make_arg_strings(self, length, idx, name):
        '''
        This makes the string of arguments for the signature of the injective lemmas:
            mkInterpInjectiveArg1 : (MkInterp _ x1) = (MkInterp _ x2) -> x1 = x2
        '''

        args1 = []
        args2 = []
        name1, name2 = name + '1', name + '2'
        for i in range(length):
            if idx == i:
                args1.append(name1)
                args2.append(name2)
            else:
                args1.append('_')
                args2.append('_')
        args1 = ' '.join(args1)
        args2 = ' '.join(args2)
        return name1, name2, args1, args2

    def generate(self):
        for vc1 in self.vcs.keys():
            for vc2 in self.vcs.keys():
                self.compare_two(vc1, vc2)

    def __str__(self):
        inj_lemmas = "\n\n".join([x[1] for x in self.injective_lemmas.values()])
        ne_lemmas = "\n\n".join([x[1] for x in self.not_equals_lemmas.values()])
        body = "\n".join(self.cases)
        return "{}\n\n{}\n\n{}\n{}".format(inj_lemmas, ne_lemmas,self.header,  body)

if __name__ == '__main__':
    parser = ArgumentParser()
    parser.add_argument('type', type=str, help="Type that we are proving deqEq for")
    parser.add_argument('valcons', type=str, nargs='+', help="A string of the form vc_name:n, where vc_name is the name of the value constructor and n is the number of arguments it takes")

    ns = parser.parse_args(argv[1:])

    tp = ns.type
    vcs = ns.valcons
    vcs = [(x[0], int(x[1])) for x in [y.split(':') for y in vcs]]

    dec = DecEqProofWriter(tp, vcs)
    dec.generate()
    print('-' * 80)
    print("-----{:^70}-----".format("BEGIN AUTOGENERATED DecEq IMPLEMENTATION FOR {}".format(tp)))
    print('-' * 80)
    print(dec)
    print('-' * 80)
    print("-----{:^70}-----".format("END AUTOGENERATED DecEq IMPLEMENTATION FOR {}".format(tp)))
    print('-' * 80)
