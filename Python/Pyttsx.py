import pyttsx3
import random

# Auto Pohai Mata (Foggy

rand_dict = {
    'people': [],
    'success': []
}

words = [('南邮还是', -30), ('people', -100), ('success', -30)]

spengine = pyttsx3.init()  
#spengine.setProperty('voice','HKEY_LOCAL_MACHINE\SOFTWARE\Microsoft\Speech\Voices\Tokens\TTS_MS_JA-JP_HARUKA_11.0')

rate = spengine.getProperty('rate')
vol = spengine.getProperty('volume')

while True:
    for word, speed in words:
        if word in rand_dict:
            lst = rand_dict[word]
            word = lst[random.randint(0, len(lst) - 1)]
        spengine.setProperty('rate', rate + speed)
        print(word)
        spengine.say(word)
    spengine.runAndWait()
