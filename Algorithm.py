def implementation(fsa_in):
    # PUT YOUR IMPLEMENTATION HERE
    fsa = fsa_in
    num_of_states = len(fsa.states)
    Rs = [[0 for x in range(3)] for y in range(3)]
    for iterator_i in range(num_of_states):
        current_state = fsa.delta[iterator_i]
        for iterator_j in range(num_of_states):
            value = []
            expr = R(3, -1, iterator_i, iterator_j)
            if iterator_j == iterator_i:
                r = R(4)
                value.append(r)
                or_ = R(2)
            for iterator_j2 in range(len(current_state)):
                if current_state[iterator_j2][0] == iterator_j:
                    if len(value) != 0: value.append(or_)
                    append = current_state[iterator_j2][1]
                    r = R(0)
                    r.set_data(append)
                    value.append(r)
            if len(value) == 0:
                r = R(1)
                value.append(r)
            expr.set_data(value)
            Rs[iterator_i][iterator_j] = expr
    for main_iterator in range(num_of_states):
        buffer_array = Rs.copy()
        Rs = [[0 for x in range(3)] for y in range(3)]
        for iterator_i in range(num_of_states):

            for iterator_j in range(num_of_states):
                expr = R(3, main_iterator, iterator_i, iterator_j)
                list = []
                var = copy.copy(buffer_array[iterator_i][main_iterator])
                list.append(var)
                var = copy.copy(buffer_array[main_iterator][main_iterator])
                var.set_kleene()
                list.append(var)
                var = copy.copy(buffer_array[main_iterator][iterator_j])
                list.append(var)
                or_ = R(2)
                list.append(or_)
                var = copy.copy(buffer_array[iterator_i][iterator_j])
                list.append(var)
                expr.set_data(list)
                expr.optimize(null_state=1, complexity=1)
                Rs[iterator_i][iterator_j] = expr
        res = str(Rs[fsa.q0][fsa.F[0]].to_string())
        result = res[1:-1]
    print('result ' + result)
    return result


import copy


class R:
    k = -1
    i = 0
    j = 0
    data = None
    is_kleene = 0

    def type(self):
        if self.is_empty_sign == 1:
            return 1
        elif self.is_or_sign == 1:
            return 2
        elif self.is_object == 1:
            return 3
        elif self.is_epsilon == 1:
            return 3
        else:
            return 0

    def to_string(self):
        global data
        if self.is_string == 1:
            return self.data
        elif self.is_object == 1:
            result = '('
            for i in range(len(self.data)):
                result = result + str(self.data[i].to_string())
            result = result + ')'
            if self.is_kleene == 1:
                result = result + '*'
            return result
        elif self.is_empty_sign == 1:
            return 'null'
        elif self.is_or_sign == 1:
            return '|'
        elif self.is_epsilon == 1:
            return 'eps'

    def set_kleene(self):
        self.is_kleene = 1

    def __init__(self, type, k=0, i=0, j=0):
        self.k = k
        self.i = i
        self.j = j
        self.is_empty_sign = 0
        self.is_or_sign = 0
        self.is_string = 0
        self.is_object = 0
        self.is_epsilon = 0
        if type == 0:
            self.is_string = 1
            self.data = ''
        if type == 1:
            self.is_empty_sign = 1
        if type == 2:
            self.is_or_sign = 1
        if type == 3:
            self.is_object = 1
            self.data = []
        if type == 4:
            self.is_epsilon = 1

    def set_data(self, input):
        global data
        if self.is_string == 1:
            self.data = input
        elif self.is_object == 1:
            for i in range(len(input)):
                self.data.append(input[i])

    def is_equal(self, expr):
        if self.is_string == 1:
            return
        elif self.is_object == 1:
            r1 = str(self.to_string()).replace("*", "")
            r2 = str(expr.to_string()).replace("*", "")
            if r1 == r2:
                return 1

    def optimize(self, null_state=0, complexity=0):
        if complexity == 1:
            i = 0
            size = len(self.data) - 1
            while i < size:
                if self.data[i].is_object == 1 and self.data[i + 1].is_object == 1:
                    if self.data[i].is_equal(self.data[i + 1]):
                        if self.data[i].if_kleene() == 0:
                            self.data[i] = None
                        elif self.data[i].is_kleene == 1:
                            self.data[i + 1] = self.data[i]
                            self.data[i] = None
                i += 1
            self.update()
        if null_state == 1:
            i = 0
            leng = len(self.data)
            while i < len(self.data):
                if self.data[i] is not None and self.data[i].is_or_sign == 0:
                    if (self.data[i].data[0].type()) == 1:
                        empty = R(1)
                        self.data[i] = empty
                        j = i + 1
                        while j < leng:
                            if self.data[j].is_or_sign == 0:
                                self.data[j] = None
                                j += 1
                            else:
                                break
                        j = i - 1
                        while j >= 0:
                            if self.data[j].is_or_sign == 0:
                                self.data[j] = None
                                j -= 1
                            else:
                                break

                i += 1
            i = 0
            self.update()
            while i < len(self.data):
                if self.data[i].is_empty_sign == 1:
                    if len(self.data) - 1 > i:
                        if self.data[i + 1].is_or_sign == 1:
                            self.data[i] = None
                            self.data[i + 1] = None
                            self.update()
                    elif 0 < i:
                        if self.data[i - 1].is_or_sign == 1:
                            self.data[i] = None
                            self.data[i - 1] = None
                            self.update()
                i += 1
            self.update()

    def if_kleene(self):
        return self.is_kleene

    def if_null(self):
        if self.to_string() == '(null)':
            return 1
        else:
            return 0

    def update(self):
        buffer = copy.copy(self.data)
        self.data.clear()
        j = 0
        while j < (len(buffer)):
            if buffer[j] is not None:
                self.data.append(buffer[j])
            j += 1
