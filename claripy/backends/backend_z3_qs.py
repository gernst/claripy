import z3
import random
from .backend_z3 import BackendZ3

MAX_LEVEL = 3

class BackendZ3QS(BackendZ3):
    def __init__(self):
        BackendZ3.__init__(self)
        self._bv_samples = None

    def _solver(self):
        return z3.Optimize(ctx=self._context)

    @staticmethod
    def _bv_count(b):
        n = b.size()
        bits = [z3.Extract(i, i, b) for i in range(n)]
        bvs = [z3.Concat(z3.BitVecVal(0, n - 1), b) for b in bits]
        nb = reduce(lambda i, j: i + j, bvs)
        return nb

    def _batch_iterate(self, expr, solver=None):
        # A collection of results (via constraint solving)
        #  and candidates (via bit flipping)
        # in the format of {value: level}
        mutations = {}

        n = expr.size()
        flippable_bits = [i for i in range(n)]
        delta = z3.BitVec('delta',  n)
        result = z3.BitVec('result', n)

        # solver = self.solver()
        solver.add(result == expr)
        solver.minimize(self._bv_count(delta))
        results = set()

        while True:
            guess = z3.BitVecVal(random.getrandbits(min(len(results), n)) if results else 0, n)

            solver.push()
            for value in mutations:
                solver.add(result != value)

            solver.add(result ^ delta == guess)


            if solver.check() != z3.sat:
                break

            model = solver.model()
            result0 = model[result].as_long()
            solver.pop()

            results.add(result0)

            yield result0
            yield None

            nresults = 0
            # From 0 to n has a low probability of finding a valid model
            # for i in range(n-1, -1, -1):
            # for i in [(n-1)*(i%2)+(i//2*(-1) if i%2 else i//2) for i in range(n)]:
            while flippable_bits:
                i = flippable_bits.pop(random.randint(0, len(flippable_bits)-1))
                # Generating a result with the ith bit flipped
                solver.push()
                goal = z3.BitVecVal(result0, n)
                solver.add(result ^ delta == goal)
                solver.add(z3.Extract(i, i, delta) == 0x1)

                if solver.check() == z3.sat:
                    model = solver.model()
                else:
                    model = None

                solver.pop()

                # Try the next bit if the model is unsat
                if not model:
                    continue

                # A new result is found by the model
                new_result = model[result].as_long()

                # Try the next bit if new result is a duplicate
                if new_result in mutations:
                    continue

                nresults += 1
                yield new_result

                # Start combining existing mutations
                new_mutations = {new_result: 1}
                # Needs at least one result in the mutations (e.g. sigma_a)
                # to combine with the new result (e.g. sigma_b)
                # When mutations is empty, this for loop will be skipped
                for existing_result in mutations:
                    # print("Combining with ", existing_result)
                    level = mutations[existing_result]
                    if level > MAX_LEVEL:
                        continue

                    candidate = (result0 ^ ((result0 ^ existing_result) |
                                            (result0 ^ new_result)))

                    # Try the next existing result in mutations if
                    # this candidate is a duplicate
                    if candidate in mutations:
                        continue

                    # The candidate is new
                    new_mutations[candidate] = level + 1
                    nresults += 1
                    yield candidate

                mutations.update(new_mutations)
                yield None  # all cheap results are generated

            if not nresults:
                break
