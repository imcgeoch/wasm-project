"""
Given a list of enum type type constructors, implement decEq
"""

def write_decEq(tp_name, val_cons):

    def write_lemma(v1, v2):
        name = "{}_not_{}".format(v1.lower(), v2)
        tp = "{} = {} -> Void".format(v1, v2)
        sig = "{} : {}".format(name, tp)
        impl = "{} Refl impossible".format(name)
        return name, '\n'.join([sig, impl])

    header = "DecEq {} where".format(tp_name)
    lemmas = {}
    impl_lines = []
    for v1 in val_cons:
        for v2 in val_cons:
            if v1 is v2:
                line = "    decEq {} {} = Yes Refl".format(v1, v2)
            elif (v2, v1) in lemmas:
                name, lemma = lemmas[(v2, v1)]
                line = "    decEq {} {} = No (negEqSym {})".format(v1, v2, name)
            else:
                name, lemma = write_lemma(v1, v2)
                lemmas[(v1, v2)] = (name, lemma)
                line = "    decEq {} {} = No {}".format(v1, v2, name)

            impl_lines.append(line)
    lems = "\n\n".join([x[1] for x in lemmas.values()])
    lines = ["-- autogen lemmas to assist implementing DecEq for {}".format(tp_name),
             lems,
             "\n\n||| autogen implementation of DecEq for {}".format(tp_name),
             header] + impl_lines

    return '\n'.join(lines)



