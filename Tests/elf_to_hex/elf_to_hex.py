import sys
import subprocess

file_in = sys.argv[1]
file_out= sys.argv[1]+".dump"

bashCommand = "riscv64-unknown-elf-objcopy -O verilog --only-section=.text "+file_in+" "+file_out
process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
output, error = process.communicate()

print(output)
print(error)

with open(file_out, 'r') as my_file:
    c = my_file.read().lower()

sections = c.split("@")

out = ""

for section in sections[1:]:
    newsection = ""
    addr_offset = (0x80000000)
    addr = (int(section.split("\n",1)[0],16)-addr_offset)
    newsection += "@"+"{0:0{1}x}".format(addr,7)+"\n"
    byte_vals = (section.split("\r\n",1)[1]).replace("\r\n", " ").split(" ")

    while(len(byte_vals)>32):
        line = ""
        for i in range(0,32):
            b = byte_vals.pop(0)
            line = b + line
        newsection += line + "\n"
    
    remaining = len(byte_vals)
    line = ""
    for i in range(0, remaining):
        b = byte_vals.pop(0)
        line = b + line
    for i in range(0, 33-remaining):
        line = "00" + line
    newsection += line+ "\n"

    out += newsection

text_file = open(sys.argv[2], "w")
n = text_file.write(out)
text_file.close()
