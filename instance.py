class Instance:
    def __init__(self, size, presents):
        self.size = size
        self.presents = presents
        self.solutions = None

    def add_solution(self, solution):
        if self.solutions is None: self.solutions = tuple()
        self.solutions += (tuple(solution), )
        return self

    def clear(self):
        self.solutions = None
        return self

    def __iter__(self): return iter(self.presents)
    def __len__(self): return len(self.presents)
    def __getitem__(self, index): return self.presents[index]
    def __str__(self): return f'Instance<{self.size[0]}x{self.size[1]}, {len(self.presents)}>'
    def __repr__(self): return str(self)
    
def read_instance_from_file(path):
    size = None
    expected_presents = None
    presents = []
    with open(path, 'r') as f: source = f.read()
    for line in source.split('\n'):
        if not line: continue
        elif size is None: size = tuple([ int(x) for x in line.split(' ') ][:2])
        elif expected_presents is None: expected_presents = int(line)
        elif len(presents) < expected_presents: presents.append(tuple([ int(x) for x in line.split(' ') ][:2]))
        else: raise Exception(f'Bad Formatted File: Too many lines @ \'{path}\'')
    return Instance(size, presents)

def write_instance_to_file(instance, path, all_solutions=True):
    if instance.solutions is None:
        output = f'### UNSATISFIABLE ###\n\n{instance.size[0]} {instance.size[1]}\n{len(instance)}\n'
        for present in instance: output += f'{present[0]} {present[1]}\n'
    elif all_solutions:
        output = f'# SOLUTIONS: {len(instance.solutions)}\n\n'
        for s, solution in enumerate(instance.solutions):
            output += f'# SOLUTION {s + 1}:\n{instance.size[0]} {instance.size[1]}\n{len(instance)}\n'
            for present, coords in zip(instance.presents, solution): output += f'{present[0]} {present[1]} {coords[0]} {coords[1]}{" (ROTATED)" if coords[2] else ""}\n'
    else:
        output = f'{instance.size[0]} {instance.size[1]}\n{len(instance)}\n'
        for present, coords in zip(instance.presents, instance.solutions[0]): output += f'{present[0]} {present[1]} {coords[0]} {coords[1]}{" (ROTATED)" if coords[2] else ""}\n'
    with open(path, 'w') as f: f.write(output)

def plot_instance(instance, all_solutions=True, block_size=20, line_size=1):
    import PIL.Image
    import numpy as np

    np.random.seed(42)
    colors = { None: True }
    def random_color(): return tuple((np.random.randint(0, 33) * 8 for _ in range(3)))
    def random_color_generator():
        while True:
            color = None
            while color in colors: color = random_color()
            colors[color] = True
            yield color
    color_generator = random_color_generator()

    if instance.solutions:
        solutions = instance.solutions if all_solutions else instance.solutions[0:1]
        n_sols = len(solutions)
        images = []
        for solution in solutions:   
            image = np.ones(shape=(*[ x * block_size for x in instance.size ], 3), dtype=np.uint8) * 255
            for (w, h), (x, y, r) in zip(instance.presents, solution):
                if r: w, h = h, w
                start_x, stop_y = (x - 1) * block_size, (instance.size[1] - y + 1) * block_size
                stop_x, start_y = start_x + w * block_size, stop_y - h * block_size
                image[start_y + line_size * 2:stop_y - line_size, start_x + line_size * 2:stop_x - line_size] = next(color_generator)
            for i in range(instance.size[0] * n_sols):
                ib = i * block_size
                image[ib:ib + line_size] = 0
            for j in range(instance.size[1] * n_sols):
                jb = j * block_size
                image[:, jb:jb + line_size] = 0
            images.append(image)
    else:
        images = np.zeros(shape=(*[x * block_size for x in instance.size ], 3), dtype=np.uint8)
    
    return [ PIL.Image.fromarray(image) for image in images ]

def plot_instance_to_file(instance, path, all_solutions=True, block_size=20, line_size=1):
    import os

    images = plot_instance(instance=instance, all_solutions=all_solutions, block_size=block_size, line_size=line_size)
    
    if all_solutions:
        dir = str.join('.', path.split('.')[:-1])
        ext = '.' + path.split('.')[-1]
        fn = os.path.join(dir, os.path.basename(path).replace(ext, '_{solution}' + ext))
        os.makedirs(dir, exist_ok=True)
        for s, image in enumerate(images):
            image.save(fn.format_map({ 'solution': s + 1 }))
    else:
        images[0].save(path.format_map({ 'solution': '' }))
    
    return images

