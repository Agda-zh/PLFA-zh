#!/usr/bin/env ruby
filename = ARGV[0]
# puts "Fixing line breaks for #{filename}"
content = File.read(filename)
REDUNDANT_LINE_BREAK_REGEX = /([\p{Han}]+)\n([\p{Han}]+)/u
while content.gsub!(REDUNDANT_LINE_BREAK_REGEX, '\1\2')
end
File.write(filename, content)
