class Word:
    def __init__(self, propVar, withoutNeg):
        self.propVar: str = propVar
        self.withoutNeg: bool = withoutNeg

    def __str__(self):
        if not self.withoutNeg:
            return "¬" + self.propVar
        else:
            return self.propVar
        
    def __eq__(self, other):
        return self.propVar == other.propVar and self.withoutNeg == other.withoutNeg
    
    def __hash__(self):
        return hash(self.propVar) ^ hash(self.withoutNeg)
    
    def __lt__(self, other):
        return self.propVar < other.propVar
    
    def __gt__(self, other):
        return self.propVar > other.propVar


# '1'
class TrueWord(Word):
    def __init__(self):
        super().__init__("1", False)

# '0'
class FalseWord(Word):
    def __init__(self):
        super().__init__("0", False)


class SimpleConjunction:
    def __init__(self, wordSet: set):
        self.wordSet: set = wordSet
        # C = W1 ∧ W2 ∧ W3 ∧ ... ∧ Wn
        self._simp()

    def __str__(self):
        if len(self.wordSet) == 0:
            return "1"
        else:
            return " ∧ ".join([str(w) for w in sorted(self.wordSet)])

    __repr__ = __str__

    def _simp(self):
        # simplify
        # if W and ¬W in C, then C = 0
        for w in self.wordSet:
            for w2 in self.wordSet:
                if w.propVar == w2.propVar and w.withoutNeg != w2.withoutNeg:
                    self.wordSet = {FalseWord()}
                    return
        # if 1 in C, then remove 1 from C
        while TrueWord() in self.wordSet and len(self.wordSet) > 1:
            self.wordSet.remove(TrueWord())
        # # if 0 in C, then C = 0
        # if FalseWord() in self.wordSet:
        #     self.wordSet = {FalseWord()}
        #     return
        
        # if length of C is 0, then C = 1
        if len(self.wordSet) == 0:
            self.wordSet = {TrueWord()}
            return
        
    def __eq__(self, other):
        return self.wordSet == other.wordSet
    
    def __hash__(self):
        return hash(frozenset(self.wordSet))


class SimpleDisjunction:
    def __init__(self, wordSet: set):
        self.wordSet: set = wordSet
        # C = W1 ∨ W2 ∨ W3 ∨ ... ∨ Wn
        self._simp()

    def __str__(self):
        if len(self.wordSet) == 0:
            return "λ"
        else:
            return " ∨ ".join([str(w) for w in sorted(self.wordSet)])

    __repr__ = __str__

    def _simp(self):
        # simplify
        # if W and ¬W in C, then C = 1
        for w in self.wordSet:
            for w2 in self.wordSet:
                if w.propVar == w2.propVar and w.withoutNeg != w2.withoutNeg:
                    self.wordSet = {TrueWord()}
                    return
        # if 0 in C, then remove 0 from C
        while FalseWord() in self.wordSet and len(self.wordSet) > 1:
            self.wordSet.remove(FalseWord())
        # # if 1 in C, then C = 1
        # if TrueWord() in self.wordSet:
        #     self.wordSet = {TrueWord()}
        #     return
        # if length of C is 0, then C = 0
        if len(self.wordSet) == 0:
            self.wordSet = {FalseWord()}
            return
        
    def __eq__(self, other):
        return self.wordSet == other.wordSet
    
    def __hash__(self):
        return hash(frozenset(self.wordSet))


class nullConjunction(SimpleConjunction):
    def __init__(self):
        super().__init__(set())
    
class nullDisjunction(SimpleDisjunction):
    def __init__(self):
        super().__init__(set())


class ConjuctiveNormalForm:
    def __init__(self, simpDisjSet: set):
        self.simpDisjSet: set = simpDisjSet
        # S = C1 ∧ C2 ∧ C3 ∧ ... ∧ Cn

    def __str__(self):
        if len(self.simpDisjSet) == 0:
            return "⊤"
        else:
            return " ∧ ".join([f'({str(c)})' for c in self.simpDisjSet])
        
    def _simp(self):
        # simplify
        # if 1 in C, then remove 1 from C
        while TrueWord() in self.wordSet and len(self.wordSet) > 1:
            self.wordSet.remove(TrueWord())
        if len(self.wordSet) == 0:
            self.wordSet = {TrueWord()}
            return


class DisjuctiveNormalForm:
    def __init__(self, simpConjSet: set):
        self.simpConjSet: set = simpConjSet
        # S = C1 ∨ C2 ∨ C3 ∨ ... ∨ Cn

    def __str__(self):
        if len(self.simpConjSet) == 0:
            return "⊥"
        else:
            return " ∨ ".join([f'({str(c)})' for c in self.simpConjSet])
        
    def _simp(self):
        # simplify
        pass


def Res(C1: SimpleDisjunction, C2: SimpleDisjunction)->SimpleDisjunction:
    wordSetC = set(C1.wordSet) | set(C2.wordSet)
    flag = False
    for l in C1.wordSet:
        for r in C2.wordSet:
            if l.propVar == r.propVar and l.withoutNeg != r.withoutNeg:
                # remove l and r from C
                wordSetC.remove(l)
                wordSetC.remove(r)
                flag = True
                break
    if not flag:
        raise Exception("C1 and C2 are not resolvable")
    C = SimpleDisjunction(wordSetC)
    return C


def ResolutionAlgorithm(S: ConjuctiveNormalForm)->bool:
    S_0 = S_2 = set()
    S_1 = S.simpDisjSet
    i = 1
    while True:
        print(f'# {i} : S0 = {S_0}, S1 = {S_1}, S2 = {S_2}')
        for C1 in S_1:
            for C2 in S_1:
                try:
                    C = Res(C1, C2)
                    if C == nullDisjunction():
                        return False
                    if C not in S_0 and C not in S_1:
                        S_2.add(C)
                except Exception:
                    continue
        for C_1 in S_1:
            for C_2 in S_1:
                if C_1 == C_2:
                    continue
                try:
                    C = Res(C_1, C_2)
                    if C == nullDisjunction():
                        return False
                    if C not in S_0 and C not in S_1:
                        S_2.add(C)
                except Exception:
                    continue
        if len(S_2) == 0:
            return True
        else:
            S_0 = S_0 | S_1
            S_1 = S_2
            S_2 = set()
            i += 1
            


if __name__ == "__main__":
    # C1 = SimpleDisjunction({Word("p", False), Word("q", True)})
    # C2 = SimpleDisjunction({Word("p", True), Word("q", True)})
    # C3 = SimpleDisjunction({Word("q", False)})

    C1 = SimpleDisjunction({Word("p", True)})
    C2 = SimpleDisjunction({Word("p", True), Word("q", True)})
    C3 = SimpleDisjunction({Word("p", True), Word("q", False)})
    C4 = SimpleDisjunction({Word("q", True), Word("r", False)})
    C5 = SimpleDisjunction({Word("q", True), Word("r", True)})

    print(f'C1 = {C1}')
    print(f'C2 = {C2}')
    print(f'C3 = {C3}')
    print(f'C4 = {C4}')
    print(f'C5 = {C5}')

    S = ConjuctiveNormalForm({C1, C2, C3, C4, C5})
    print(f'S = {S}')

    result = ResolutionAlgorithm(S)
    if result:
        print("S is satisfiable")
    else:
        print("S is not satisfiable")
