package info.kwarc.sally.networking.cometd;

import java.util.Set;
import java.util.regex.Pattern;

import org.reflections.Reflections;
import org.reflections.scanners.ResourcesScanner;
import org.reflections.util.ClasspathHelper;
import org.reflections.util.ConfigurationBuilder;

public class ReflectionTest {
	public static void main(String[] args) {
		Reflections reflections = new Reflections(new ConfigurationBuilder()
		.addUrls(ClasspathHelper.forPackage("sally"))
				.setScanners(new ResourcesScanner()));

		Set<String> propertiesFiles = reflections.getResources(Pattern.compile(".*"));
		System.out.println(propertiesFiles.size());
		for (String file : propertiesFiles) {
			System.out.println(file);
		}
	}	
}
