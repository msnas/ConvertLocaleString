/*
	N041

	Author: 		msnas
	Description:	Changes the ChatPacket to LocaleChatPacket + converts locale_string.txt from serverside to clientside

	Changes:
		msnas			02/05/2022 to 05/05/2022 - Created the base
		msnas			06/05/2022 - Checked every chat packet (only verifying the CHAT_TYPE_INFO
		msnas			06/05/2022 - Changed the ChatPacket(CHAT_TYPE_INFO, LC_TEXT("abc %d") to LocaleChatPacket(CHAT_TYPE_INFO, count, "abc")
		msnas			06/05/2022 - Created a logs.txt with all the texts that doesn't exist on locale_string.txt 
		msnas			08/05/2022 - Rewrited the code in order to boost performance
		msnas			08/05/2022 - If the text isn't translated, don't convert it nor change it.
*/

#define FMT_HEADER_ONLY
#define NUM_LOCALES 2
#define CHAT_TYPE_COUNT 6

#include <fmt/color.h>
#include <string>
#include <iostream>
#include <fstream>
#include <sstream>
#include <filesystem>
#include <map>
#include <regex>
#include <chrono>

namespace fs = std::filesystem;
std::chrono::steady_clock::time_point t1, t2;

using std::chrono::high_resolution_clock;
using std::chrono::duration_cast;
using std::chrono::duration;
using std::chrono::minutes;
using std::chrono::seconds;

std::map<std::string, std::string> localeString;
std::map<int, std::map<std::string, std::string>> localeMap;
std::map<std::string, std::map<int, std::string>> missingString;
std::map<std::string, std::map<int, std::string>> notLocaleString;

// What are the types we're trying to find?
const char* ChatTypes[CHAT_TYPE_COUNT] = {
	"CHAT_TYPE_TALKING",
	"CHAT_TYPE_INFO",
	"CHAT_TYPE_NOTICE",
	"CHAT_TYPE_PARTY",
	"CHAT_TYPE_GUILD",
	"CHAT_TYPE_DICE_INFO",
};

// REMOVED FROM METIN SOURCE CODE - BEGIN
void locale_add(const char** strings)
{
	auto iter = localeString.find(strings[0]);
	if (iter == localeString.end())
		localeString.insert(std::make_pair(strings[0], strings[1]));

}

const char* quote_find_end(const char* string)
{
	const char* tmp = string;
	int         quote = 0;

	while (*tmp)
	{
		if (quote && *tmp == '\\' && *(tmp + 1))
		{
			// \ 다음 문자가 " 면 스킵한다.
			switch (*(tmp + 1))
			{
			case '"':
				tmp += 2;
				continue;
			}
		}
		else if (*tmp == '"')
		{
			quote = !quote;
		}
		else if (!quote && *tmp == ';')
			return (tmp);

		tmp++;
	}

	return (NULL);
}

char* locale_convert(const char* src, int len)
{
	const char* tmp;
	int		i, j;
	char* buf, * dest;
	int		start = 0;
	char	last_char = 0;

	if (!len)
		return NULL;

	buf = new char[len + 1];

	for (j = i = 0, tmp = src, dest = buf; i < len; i++, tmp++)
	{
		if (*tmp == '"')
		{
			if (last_char != '\\')
				start = !start;
			else
				goto ENCODE;
		}
		else if (*tmp == ';')
		{
			if (last_char != '\\' && !start)
				break;
			else
				goto ENCODE;
		}
		else if (start)
		{
		ENCODE:
			if (*tmp == '\\' && *(tmp + 1) == 'n')
			{
				*(dest++) = '\n';
				tmp++;
				last_char = '\n';
			}
			else
			{
				*(dest++) = *tmp;
				last_char = *tmp;
			}

			j++;
		}
	}

	if (!j)
	{
		delete[] buf;
		return NULL;
	}

	*dest = '\0';
	return (buf);
}

void LoadLocaleString()
{
	auto locale = fs::current_path().u8string() + "\\locale_string.txt";
	FILE* fp = fopen(locale.c_str(), "rb");
	char* buf;

	if (!fp)
	{
		std::cout << "LoadLocaleString: The file couldn't be open" << std::endl;
		return;
	}


	fseek(fp, 0L, SEEK_END);
	int i = ftell(fp);
	fseek(fp, 0L, SEEK_SET);

	i++;

	buf = new char[i];

	memset(buf, 0, i);

	fread(buf, i - 1, sizeof(char), fp);

	fclose(fp);

	const char* tmp;
	const char* end;

	char* strings[NUM_LOCALES];

	if (!buf)
		exit(1);


	tmp = buf;

	do
	{
		for (i = 0; i < NUM_LOCALES; i++)
			strings[i] = NULL;

		if (*tmp == '"')
		{
			for (i = 0; i < NUM_LOCALES; i++)
			{
				if (!(end = quote_find_end(tmp)))
					break;

				strings[i] = locale_convert(tmp, end - tmp);
				tmp = ++end;

				while (*tmp == '\n' || *tmp == '\r' || *tmp == ' ') tmp++;

				if (i + 1 == NUM_LOCALES)
					break;

				if (*tmp != '"')
					break;
			}

			if (strings[0] == NULL || strings[1] == NULL)
				break;

			locale_add((const char**)strings);

			for (i = 0; i < NUM_LOCALES; i++)
				if (strings[i])
					delete[] strings[i];
		}
		else
		{
			tmp = strchr(tmp, '\n');

			if (tmp)
				tmp++;
		}
	} while (tmp && *tmp);
}
// REMOVED FROM METIN SOURCE CODE - END

// Function to replace the string with the condition from and to
bool replace(std::string& str, const std::string& from, const std::string& to) {
	size_t start_pos = str.find(from);
	if (start_pos == std::string::npos)
		return false;
	str.replace(start_pos, from.length(), to);
	return true;
}

// Get the string between strings using regex
std::string GetBetweenStrings(const std::string& line, std::string beg, std::string end)
{
	using namespace std::string_literals;
	std::regex base_regex(beg + "(.*)" + end);
	std::smatch base_match;
	std::string matched;

	if (std::regex_search(line, base_match, base_regex)) {
		if (base_match.size() == 2) {
			matched = base_match[1].str();
		}
	}

	return matched;
}

// Start the clock to get the time elapsed
void StartTime() { t1 = high_resolution_clock::now(); }

// Function that returns the minutes and seconds since the clock started
std::pair<std::chrono::minutes, std::chrono::seconds> GetTimeElapsed()
{
	t2 = high_resolution_clock::now();

	auto min = duration_cast<minutes>(t2 - t1);
	auto sec = duration_cast<seconds>(t2 - t1);

	return std::make_pair(min, sec);
}

// Creates the locale_string.txt with the values from the localeMap 
void CreateLocaleString()
{
	std::ofstream localeStr(fs::current_path().u8string() + "\\bin\\locale_string.txt");
	if (localeStr.is_open())
	{
		for (auto it = localeMap.begin(); it != localeMap.end(); it++)
		{
			for (auto itLocaleSec = it->second.begin(); itLocaleSec != it->second.end(); itLocaleSec++)
				localeStr << it->first << "\t" << itLocaleSec->second << "\n";
		}

		localeStr.close();
	}
}

// Crates the missing.txt where it shows what are the texts that aren't translated
void CreateMissingLog()
{
	std::ofstream missing(fs::current_path().u8string() + "\\bin\\missing.txt");
	if (missing.is_open())
	{
		if (missingString.size())
		{
			fmt::print(fmt::emphasis::bold | fg(fmt::color::red), "The file missing.txt was created, verify what are the texts that needs to be edit on locale_string.txt\n");

			for (auto it = missingString.begin(); it != missingString.end(); it++)
			{
				for (auto secIt = it->second.begin(); secIt != it->second.end(); secIt++)
					missing << "[" << it->first << "] line " << secIt->first << ": " << secIt->second << "\n";
			}
		}
		missing.close();
	}
}


// Crates the notlocale_string.txt where it shows what are the texts that doesn't have LC_TEXT
void CreateNotLocaleString()
{
	std::ofstream notlocale(fs::current_path().u8string() + "\\bin\\notlocale_string.txt");
	if (notlocale.is_open())
	{
		if (notLocaleString.size())
		{
			fmt::print(fmt::emphasis::bold | fg(fmt::color::orange), "The file notlocale_string.txt was created, verify what are the texts you want to translate.\n");

			for (auto it = notLocaleString.begin(); it != notLocaleString.end(); it++)
			{
				for (auto secIt = it->second.begin(); secIt != it->second.end(); secIt++)
					notlocale << "[" << it->first << "] line " << secIt->first << ": " << secIt->second << "\n";
			}
		}
		notlocale.close();
	}
}

void CheckMissingString(std::string text, std::string fileName, int lineCount)
{
	// Doesn't matter how many times it shows up, we only need 1 record
	bool added = true;
	for (auto it = missingString.begin(); it != missingString.end(); it++)
	{
		for (auto it_ = it->second.begin(); it_ != it->second.end(); it_++)
		{
			if (it_->second == text)
				added = false;
		}
	}

	if (added)
		missingString[fileName][lineCount] = text;
}

void CheckNotLocaleString(std::string text, std::string fileName, int lineCount)
{
	// Doesn't matter how many times it shows up, we only need 1 record
	bool added = true;
	for (auto it = notLocaleString.begin(); it != notLocaleString.end(); it++)
	{
		for (auto it_ = it->second.begin(); it_ != it->second.end(); it_++)
		{
			if (it_->second == text)
				added = false;
		}
	}

	if (added)
		notLocaleString[fileName][lineCount] = text;
}

int main()
{
	StartTime(); // Starts the clock

	// Load the locale string
	std::cout << "Loading Locale String..." << "\n";
	LoadLocaleString();

	auto dir = fs::current_path().u8string() + "\\input"; // Gets the directory and the folder input
	int count = 0; // Variable to count the ids going on the locale_string.txt

	for (const auto& entry : fs::directory_iterator(dir))
	{
		// If the file is a .cpp
		if (entry.path().extension().u8string() == ".cpp")
		{
			int lineCount = 1; // Get the line count from the folder [starts at 1]
			int affectedLines = 0; // How many lines were affected by the changes?

			std::string line; // This variable will get the line of the file
			auto fileName = entry.path().filename().u8string(); // Get the name of the file

			// Open the file and create the new one on the output folder
			// 
			std::ifstream fileInput(entry.path());
			std::ofstream fileOutput(fs::current_path().u8string() + "\\output\\" + fileName);

			const std::size_t buf_size = 32768;
			char my_buffer[buf_size];
			fileOutput.rdbuf()->pubsetbuf(my_buffer, buf_size);

			if (fileInput.is_open())
			{
				std::string textInput;
				while (getline(fileInput, line)) // Get the line and insert on the string "line"
				{
					std::string number; // Variable that will recieve either the number assigned to the text or the count
					auto between = GetBetweenStrings(line, "\"", "\"");
					if (!between.empty())
					{
						// In the localeMap map, we'll verify if the second's second value is the same as the variable "between"
						// This means that if the text is the same as the "between"
						// If so, the second's first value will be assigned to "number"
						for (auto itLocale = localeMap.begin(); itLocale != localeMap.end(); itLocale++)
						{
							for (auto itLocaleSec = itLocale->second.begin(); itLocaleSec != itLocale->second.end(); itLocaleSec++)
							{
								if (itLocaleSec->first == between)
									number = std::to_string(itLocale->first);
							}
						}

						// If it's empty, meaning that there's no number to assign it, it will get the count
						if (number.empty())
							number = std::to_string(count);

						for (int i = 0; i < CHAT_TYPE_COUNT; i++)
						{
							auto type = std::string(ChatTypes[i]);

							// Search for the 'ChatPacket(type, LC_TEXT("' and 'ChatPacket(type, "'
							auto textWithLC = "ChatPacket(" + type + ", LC_TEXT(\"" + between + "\")";
							auto textWithoutLC = "ChatPacket(" + type + ", \"";

							// Finds if the text exists on the locale_string.txt from the serverside
							if (localeString.find(between) != localeString.end())
							{
								// If it founds and replaces
								if (replace(line, textWithLC, "LocaleChatPacket(" + type + ", " + number + ", \"" + between + "\""))
								{

									// If the number doesn't exist on the localeMap, creates one and add +1 on the count
									if (localeMap.find(stoi(number)) == localeMap.end())
									{
										localeMap[stoi(number)][between] = localeString.at(between);
										count++;
									}

									fmt::print("[{}] line {} changed\n", format(fg(fmt::color::dark_orange), fileName), format(fg(fmt::color::yellow_green), std::to_string(lineCount)));
									affectedLines++;
								}
							}
							else
							{
								if (size_t pos = line.find(textWithLC) != std::string::npos)
									CheckMissingString(between, fileName, lineCount); // Verify if the text already is on the missingString.
							}

							// If string isn't LC_TEXT, we'll add to another file called notlocale_string.txt
							if (size_t pos = line.find(textWithoutLC) != std::string::npos)
								CheckNotLocaleString(between, fileName, lineCount);
						}
					}

					textInput += line + '\n'; // Insert the line to variable "textInput"
					lineCount++; // Adding +1 to the line
				}

				fileInput.close(); // Closes the file
				fileOutput << textInput << "\n"; // The new file will have all the data from "textInput"

				fmt::print("File {} completed ({} lines affected).\n", format(fg(fmt::color::green), fileName), format(fg(fmt::color::gold), std::to_string(affectedLines)));
			}
		}
	}

	// Creates the locale_string.txt, missing.txt and notlocale_string.txt
	CreateLocaleString();
	CreateMissingLog();
	CreateNotLocaleString();

	// Gets and outputs the time elapsed with minutes and seconds
	auto time = GetTimeElapsed();
	if (time.first.count() > 0)
		fmt::print(fmt::emphasis::bold | fg(fmt::color::green), "Time elapsed: {}:{} minutes\n", time.first.count(), time.second.count());
	else
		fmt::print(fmt::emphasis::bold | fg(fmt::color::green), "Time elapsed: {} seconds\n", time.second.count());

#ifndef _DEBUG
	system("pause");
#endif
	return 0;
}