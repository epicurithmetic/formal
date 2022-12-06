from PIL import Image, ImageDraw, GifImagePlugin

# Read in the output of the computation.
computation_file = open("tm-output.txt","r")
computation_raw = computation_file.read()
computation_raw = computation_raw.split("\n")

def computation_configurations(raw_computation):

    """
        Given a .txt file output from tmMain.py 
        this function splits the file into a list whose
        elements are the distinct configurations of the 
        corresponding computation.
    
    """

    # Initialise storage of configurations.
    list_of_configurations = []

    # Measure number of configurations. 
    number_of_configurations = len(raw_computation)//10

    # Iterate over configurations and append them to storage.
    configuration = 0
    while configuration < number_of_configurations:

        lower = 0 + 10*configuration
        upper = 10 + 10*configuration
        current_configuration = raw_computation[lower:upper]
        list_of_configurations.append(current_configuration)
        configuration += 1

    return list_of_configurations

def tape_configuration_image(configuration,output_name):

    """
        Given a 10-line computation generate from tmMain.py
        and the method computation_configurations, this 
        function saves an image of the 10-line configuration.
    
    """

    # Create a new image to store the computation on. 
    computation_image = Image.new("L", (420,100))    

    # Setup the drawing. 
    draw = ImageDraw.Draw(computation_image)

    # Set each line onto the image. Use shift to set new lines.
    shift = 0
    for line in configuration:
        draw.text((0,0 + shift*10),line,fill=255)
        shift += 1

    computation_image.save(output_name)
    print("Image saved as: " + output_name)

# Split the configurations into a list.
computation_configurations_list = computation_configurations(computation_raw) 

# Number of frames
number_of_frames = len(computation_configurations_list)

# Iterate over the list to create images for each computation. 
# Set a counter to distinguish names of image files. 
image = 1
for config in computation_configurations_list:

    output_title = "images/kiaora_" + str(image) + ".png"

    tape_configuration_image(config,output_title)

    image += 1


# These instructions compile the .gif from existing images. 
frames = []
frame_count = 1
while frame_count < number_of_frames:
    frame = Image.open("images/kiaora_" + str(frame_count) + ".png")
    frames.append(frame)
    frame_count += 1

# Save the .gif   
frames[0].save("images/kiaora.gif",save_all=True,
    append_images=frames[1:],duration=750,loop=1)
