if __name__ == '__main__':
    import os
    import argparse
    import importlib
    from instance import read_instance_from_file, write_instance_to_file, plot_instance_to_file
    

    print('================================================================')
    print('================================================================')
    print('===                 Present Wrapping Problem                 ===')
    print('===      Combinatorial Decision Making and Optimization      ===')
    print('===       Group: Nicola Amoriello, Daniele Domenichelli      ===')
    print('================================================================')
    print('================================================================')
    print('')
    
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument('-m', '--method', required=True, type=str, help='Method used to carry out the solution(s), possible: CP, SAT, SMT')
    arg_parser.add_argument('-i', '--input', action='append', default=[], help='Files or directories where to locate the problem instaces')
    arg_parser.add_argument('-o', '--output', default=None, type=str, help='Directory where to store the outputs')
    arg_parser.add_argument('-img', '--images', default=None, type=str, help='Directory where to store the image representations of the outputs')
    arg_parser.add_argument('-ni', '--no-images', nargs='?', default=False, const=True, help='Prevent the generation of the image representation')
    arg_parser.add_argument('-s', '--all-solutions', nargs='?', default=False, const=True, help='Get all the solutions for each instance of the problem')
    try: args = arg_parser.parse_args()
    except: arg_parser.print_help(), exit(1)

    args.method = str(args.method or '').strip().upper()
    methods = ('CP', 'SAT', 'SMT')
    if args.method not in methods: print(f'ERROR: The given method \'{args.method}\' is not supported!'), exit(1)
    
    try: resolver = importlib.import_module(f'{args.method}.main').main
    except Exception as e: print(f'ERROR: Error during the loading of the given method'), print(e), exit(1)

    if args.output is None: args.output = os.path.join(args.method, 'out')
    if args.images is None: args.images = os.path.join(os.path.dirname(args.output), 'images')
    if not len(args.input): args.input = [ 'instances' ]
    
    all_solutions = args.all_solutions

    instance_files = []
    for path in args.input:
        if not os.path.exists(path): print(f'ERROR: Input file \'{path}\' does not exists!'), exit(1)
        elif os.path.isdir(path): instance_files += [ os.path.join(path, file) for file in os.listdir(path) ]
        else: instance_files.append(path)
    
    output_files = [ os.path.join(args.output, os.path.basename(file).replace('.txt', '-out.txt')) for file in instance_files ]
    images_files = [ os.path.join(args.images, os.path.basename(file).replace('.txt', '.png')) for file in instance_files ]
    
    try: instances = [ read_instance_from_file(file) for file in instance_files ]
    except Exception as e: print(f'ERROR: Error while parsing the input files'), print(e), exit(1)

    # try:
    for instance, output, image_output in zip(instances, output_files, images_files):
        print(f'Solving instance: {instance}')
        resolver(instance, all_solutions=all_solutions)
        print(f'Solutions: {len(instance.solutions)}' if instance.solutions else 'Solutions: 0')
        print('Writing solutions...')
        write_instance_to_file(instance, output, all_solutions=all_solutions)
        if not args.no_images:
            print('Generating images...')
            plot_instance_to_file(instance, image_output, all_solutions=all_solutions)
    # except Exception as e: print(f'ERROR: Error during the execution of the given method'), print(e), exit(1)
    
     
    
