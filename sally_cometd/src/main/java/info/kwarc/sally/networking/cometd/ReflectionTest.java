package info.kwarc.sally.networking.cometd;

import java.util.Set;
import java.util.regex.Pattern;

import org.reflections.Reflections;

public class ReflectionTest {
	public static void main(String[] args) {
        Reflections reflections = new Reflections("");
        Set<String> properties = reflections.getResources(Pattern.compile(".*"));
        System.out.println(properties.size());
	}
}
